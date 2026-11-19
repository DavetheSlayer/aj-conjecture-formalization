import Mathlib
import AJFamily.Quantum.NodeCollision
import AJFamily.Quantum.EbNodeCollision
import AJTwist.Factor.TwFBlocksPullback
import AJTwist.Factor.TwFNegSymbolValues
import AJTwist.Factor.TwFNegEval
import AJTwist.Factor.TwFNegEbNode

import AJTwist.Factor.TwFNegEbFacts

/-!
# The crossing `E/C_b`: the fibre (TwF, unit F2)

Source: revision 5, Section 5.2 (`operators.tex`): "At `Z = -2` the varying block fixes
`e = (2a + 1)/a`, and then `(J - 1) e = -4` fixes `J` uniquely. … Each entire meridian fiber has
only the indicated meeting of distinct blocks."

`twNeg_ebNode_collisionFree`: on the fibre `M = m₀` of the `E/C_b` node the blocks `E` and `C_b`
meet only at `l₀ = twNegNodeL b m₀`, and `L = 1` is a zero of neither
(`NodeCollisionFree extraFactor (twistPolyNeg b) (X - 1) m₀ l₀`).

Route (as `ebNode_collisionFree`, `eq_ebNodeL_of_extraFactor_twistPoly`,
`AJFamily/Quantum/EbNodeCollision.lean`). A common zero `l` of `E` and `C_b` on the fibre has
`l + x₀ ≠ 0` (`eval_neg_twistPolyNeg`), and with `J = (x₀ l + 1)/(l + x₀)`: `Z(K, J) = -2`
(`twfPullback_symbolZeta_add`, `evalIntPoint_twfPullback`) and `T_(-b)(K, J) = 0`
(`evalEval_twistPolyNeg`); by `famTKNeg_of_famZK_eq_neg_two`, `K - J = -(b - 1)/b`, and
`Z = 1 + K - K J + J² = -2` then gives `(2b - 1) J = -(2b + 1)`, i.e. `J = J₀`, so `l = l₀`
(the Möbius map is injective). At `L = 1`: `E(m₀, 1) = 4 m₀² ≠ 0`,
`C_b(m₀, 1) = (1 + x₀)^(2b-1) x₀^b (b K - 2b + 1) ≠ 0` (`famTKNeg_one`; `K ≠ 2 - 1/b` on this
fibre), and `∂_L (L - 1) = 1`.
Checked for `b ≤ 6` modulo a prime (scratch `check_node_facts.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `(L - 1)(m, l) = l - 1`. -/
private theorem evalIntPoint_X_sub_one_twfNegEbCollision (m l : ℂ) :
    evalIntPoint (X - 1) m l = l - 1 := by
  rw [evalIntPoint_eq_evalEval]
  simp

/-- On the fibre of the `E/C_b` node, `b(2b - 1) K = -(4b² - 2b + 1)`. -/
private theorem famKQ_ebNode_twfNegEbCollision (b : ℕ) {m₀ : ℂ}
    (heb : (b : ℂ) * (2 * b - 1) * (m₀ ^ 2) ^ 2 + (4 * b ^ 2 - 2 * b + 1) * m₀ ^ 2 +
      b * (2 * b - 1) = 0) (h0 : m₀ ≠ 0) :
    (b : ℂ) * (2 * b - 1) * famKQ (m₀ ^ 2) = -(4 * b ^ 2 - 2 * b + 1) := by
  have hx0 : m₀ ^ 2 ≠ 0 := pow_ne_zero 2 h0
  simp only [famKQ]
  field_simp
  linear_combination heb

/-- At the `E/C_b` node, a common zero of the `E`- and `C_b`-fibres is `L₀`. -/
private theorem eq_twNegNodeL_of_extraFactor_twistPolyNeg (b : ℕ) (hb : 1 ≤ b) {m₀ l : ℂ}
    (heb : (b : ℂ) * (2 * b - 1) * (m₀ ^ 2) ^ 2 + (4 * b ^ 2 - 2 * b + 1) * m₀ ^ 2 +
      b * (2 * b - 1) = 0) (h0 : m₀ ≠ 0) (h1 : m₀ ^ 2 ≠ 1) (hxJ : m₀ ^ 2 ≠ twNegNodeJ b)
    (hT : l ^ 2 - ((m₀ ^ 2) ^ 2 - 4 * m₀ ^ 2 + 1) * l + (m₀ ^ 2) ^ 2 = 0)
    (hB : evalIntPoint (twistPolyNeg b) m₀ l = 0) :
    l = twNegNodeL b m₀ := by
  have hx0 : m₀ ^ 2 ≠ 0 := pow_ne_zero 2 h0
  have hx1 : m₀ ^ 2 - 1 ≠ 0 := sub_ne_zero.2 h1
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have h2b : 2 * (b : ℂ) - 1 ≠ 0 := by
    intro h
    have h' : ((2 * b : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
      push_cast
      linear_combination h
    have := Nat.cast_injective h'
    omega
  have hL : l + m₀ ^ 2 ≠ 0 := by
    intro h
    have hl : l = -m₀ ^ 2 := by linear_combination h
    rw [hl] at hT
    have : m₀ ^ 2 * (m₀ ^ 2 - 1) ^ 2 = 0 := by linear_combination hT
    exact mul_ne_zero hx0 (pow_ne_zero 2 hx1) this
  rw [evalIntPoint_eq_evalEval, evalEval_twistPolyNeg h0 hL hb] at hB
  have hB' := (mul_eq_zero.1 hB).resolve_left
    (mul_ne_zero (pow_ne_zero _ hL) (pow_ne_zero _ hx0))
  have hK := famKQ_ebNode_twfNegEbCollision b heb h0
  set K := famKQ (m₀ ^ 2) with hKdef
  set J := (m₀ ^ 2 * l + 1) / (l + m₀ ^ 2) with hJdef
  have hJl : J * (l + m₀ ^ 2) = m₀ ^ 2 * l + 1 := by
    rw [hJdef]
    field_simp
  have hZ : famZK K J = -2 := by
    simp only [famZK, hKdef, hJdef, famKQ]
    field_simp
    linear_combination (m₀ ^ 2 + 1) ^ 2 * hT
  rw [famTKNeg_of_famZK_eq_neg_two b hb hZ] at hB'
  have hJ : (b : ℂ) * (K - J) + b - 1 = 0 :=
    (mul_eq_zero.1 hB').resolve_left (pow_ne_zero _ (by norm_num))
  have hJ0 : (2 * (b : ℂ) - 1) * J = -(2 * b + 1) := by
    refine mul_left_cancel₀ hb0 ?_
    linear_combination hK - (2 * (b : ℂ) - 1) * hJ
  have hJe : J = twNegNodeJ b := by
    rw [twNegNodeJ, eq_div_iff h2b]
    linear_combination hJ0
  have hd : twNegNodeJ b - m₀ ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hxJ)
  rw [twNegNodeL, famNodeL, eq_div_iff hd, ← hJe]
  linear_combination hJl

/-- At the `E/C_b` node, `C_b(m₀, 1) ≠ 0`. -/
private theorem twistPolyNeg_one_ne_zero_ebNode (b : ℕ) (hb : 1 ≤ b) {m₀ : ℂ}
    (heb : (b : ℂ) * (2 * b - 1) * (m₀ ^ 2) ^ 2 + (4 * b ^ 2 - 2 * b + 1) * m₀ ^ 2 +
      b * (2 * b - 1) = 0) (h0 : m₀ ≠ 0) (h2 : m₀ ^ 2 ≠ -1) :
    evalIntPoint (twistPolyNeg b) m₀ 1 ≠ 0 := by
  have hx0 : m₀ ^ 2 ≠ 0 := pow_ne_zero 2 h0
  have hL : (1 : ℂ) + m₀ ^ 2 ≠ 0 := by
    intro h
    exact h2 (by linear_combination h)
  rw [evalIntPoint_eq_evalEval, evalEval_twistPolyNeg h0 hL hb]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hL) (pow_ne_zero _ hx0)) ?_
  have hJ : (m₀ ^ 2 * 1 + 1) / (1 + m₀ ^ 2) = 1 := by
    rw [div_eq_one_iff_eq hL]
    ring
  have hK := famKQ_ebNode_twfNegEbCollision b heb h0
  rw [hJ, famTKNeg_one b hb]
  intro h
  have hpos : (8 * (b : ℂ) ^ 2 + 2 : ℂ) = 6 * b := by
    linear_combination hK - (2 * (b : ℂ) - 1) * h
  have hnat : 8 * b ^ 2 + 2 = 6 * b := by exact_mod_cast hpos
  nlinarith

/-- The `E/C_b` node is collision free. -/
theorem twNeg_ebNode_collisionFree (b : ℕ) (hb : 1 ≤ b) {m₀ : ℂ}
    (heb : (b : ℂ) * (2 * b - 1) * (m₀ ^ 2) ^ 2 + (4 * b ^ 2 - 2 * b + 1) * m₀ ^ 2 +
      b * (2 * b - 1) = 0) :
    NodeCollisionFree extraFactor (twistPolyNeg b) (X - 1) m₀ (twNegNodeL b m₀) := by
  obtain ⟨h0, h1, h2, hxJ, -⟩ := twNeg_ebNode_facts b hb heb
  have hx0 : m₀ ^ 2 ≠ 0 := pow_ne_zero 2 h0
  refine ⟨fun l hG hD ↦ ?_, fun l hT ↦ ?_⟩
  · rw [evalIntPoint_extraFactor] at hG
    exact eq_twNegNodeL_of_extraFactor_twistPolyNeg b hb heb h0 h1 hxJ hG hD
  rw [evalIntPoint_X_sub_one_twfNegEbCollision] at hT
  have hl : l = 1 := by linear_combination hT
  subst hl
  refine ⟨?_, twistPolyNeg_one_ne_zero_ebNode b hb heb h0 h2, ?_⟩
  · rw [evalIntPoint_extraFactor]
    intro h
    exact mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hx0 (by linear_combination h)
  · rw [evalIntPoint_derivative_X_sub_one]
    exact one_ne_zero

end AJConjecture
