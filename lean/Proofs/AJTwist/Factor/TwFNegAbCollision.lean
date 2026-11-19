import Mathlib
import AJFamily.Quantum.NodeCollision
import AJFamily.Quantum.EbNodeCollision
import AJTwist.Factor.TwFBlocksPullback
import AJTwist.Factor.TwFNegSymbolValues
import AJTwist.Factor.TwFNegEval

import AJTwist.Factor.TwFNegAbFacts

/-!
# The crossing `(L - 1)/C_b`: the fibre (TwF, unit F2)

Source: revision 5, Section 5.2 (`operators.tex`): "At `J = 1` the value `Z = 2` separates `L - 1`
from `E`. … Each entire meridian fiber has only the indicated meeting of distinct blocks."

`twNeg_abNode_collisionFree`: on the fibre `M = m₀` of the abelian node of `P_(-b)`
(`b x₀² - (2b - 1) x₀ + b = 0`, `x₀ = m₀²`, `K = 2 - 1/b`) the blocks `L - 1` and `C_b` meet only
at `L = 1`, and the two zeros of `E` are simple and are zeros of neither `L - 1` nor `C_b`
(`NodeCollisionFree (X - 1) (twistPolyNeg b) extraFactor m₀ 1`).

Route (as `abNode_collisionFree`, `AJFamily/Quantum/AbNodeCollision.lean`). The first clause is
trivial. For a zero `l` of `E(m₀, ·)`: `E(m₀, 1) = 4 m₀² ≠ 0` so `l ≠ 1`; the discriminant of `E`
is `(x - 1)² (x² - 6x + 1)`, nonzero since `K ≠ 2, 6`, so `∂_L E ≠ 0`; and `C_b(m₀, l) ≠ 0`:
if `l = -x₀` then `C_b(m₀, l) = x₀^b (x₀² - 1)^(2b-1) ≠ 0` (`eval_neg_twistPolyNeg`); otherwise,
with `J = (x₀ l + 1)/(l + x₀)`, a common zero has `Z = -2`
(`(x + 1)² E` is the pullback of `ζ + 2x`, `twfPullback_symbolZeta_add`,
`evalIntPoint_twfPullback`) and `T_(-b)(K, J) = 0` (`evalEval_twistPolyNeg`), hence by
`famTKNeg_of_famZK_eq_neg_two` `K - J = -(b - 1)/b`, and with `Z = -2` this gives
`K = -2 - 1/(b(2b - 1))`, which differs from `2 - 1/b` (`8b² - 6b + 2 ≠ 0`).
Checked for `b ≤ 6` modulo a prime (scratch `check_node_facts.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `(L - 1)(m, l) = l - 1`. -/
private theorem evalIntPoint_X_sub_one_twfNegAbCollision (m l : ℂ) :
    evalIntPoint (X - 1) m l = l - 1 := by
  rw [evalIntPoint_eq_evalEval]
  simp

/-- At the abelian node of `P_(-b)`, `C_b` does not vanish at a zero of the `E`-fibre. -/
private theorem twistPolyNeg_ne_zero_of_extraFactor_abNode (b : ℕ) (hb : 1 ≤ b) {m₀ l : ℂ}
    (hab : (b : ℂ) * (m₀ ^ 2) ^ 2 - (2 * b - 1) * m₀ ^ 2 + b = 0) (h0 : m₀ ≠ 0)
    (h1 : m₀ ^ 2 ≠ 1)
    (hT : l ^ 2 - ((m₀ ^ 2) ^ 2 - 4 * m₀ ^ 2 + 1) * l + (m₀ ^ 2) ^ 2 = 0) :
    evalIntPoint (twistPolyNeg b) m₀ l ≠ 0 := by
  have hx0 : m₀ ^ 2 ≠ 0 := pow_ne_zero 2 h0
  have hx1 : m₀ ^ 2 - 1 ≠ 0 := sub_ne_zero.2 h1
  have hL : l + m₀ ^ 2 ≠ 0 := by
    intro h
    have hl : l = -m₀ ^ 2 := by linear_combination h
    rw [hl] at hT
    have : m₀ ^ 2 * (m₀ ^ 2 - 1) ^ 2 = 0 := by linear_combination hT
    exact mul_ne_zero hx0 (pow_ne_zero 2 hx1) this
  rw [evalIntPoint_eq_evalEval, evalEval_twistPolyNeg h0 hL hb]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hL) (pow_ne_zero _ hx0)) ?_
  set K := famKQ (m₀ ^ 2) with hKdef
  set J := (m₀ ^ 2 * l + 1) / (l + m₀ ^ 2) with hJdef
  have hZ : famZK K J = -2 := by
    simp only [famZK, hKdef, hJdef, famKQ]
    field_simp
    linear_combination (m₀ ^ 2 + 1) ^ 2 * hT
  have hZ' : J ^ 2 - K * J + K + 3 = 0 := by
    simp only [famZK] at hZ
    linear_combination hZ
  have hK : (b : ℂ) * K = 2 * b - 1 := by
    simp only [hKdef, famKQ]
    field_simp
    linear_combination hab
  rw [famTKNeg_of_famZK_eq_neg_two b hb hZ]
  intro h
  have hJ : (b : ℂ) * (K - J) + b - 1 = 0 :=
    (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ (by norm_num))
  have hJ' : (b : ℂ) * J = 3 * b - 2 := by linear_combination hK - hJ
  have hpos : (8 * (b : ℂ) ^ 2 + 2 : ℂ) = 6 * b := by
    linear_combination (b : ℂ) ^ 2 * hZ' - (b * J + 3 * b - 2 - (2 * b - 1)) * hJ' +
      (b * J - b) * hK
  have hnat : 8 * b ^ 2 + 2 = 6 * b := by exact_mod_cast hpos
  nlinarith

/-- The abelian node of `P_(-b)` is collision free. -/
theorem twNeg_abNode_collisionFree (b : ℕ) (hb : 1 ≤ b) {m₀ : ℂ}
    (hab : (b : ℂ) * (m₀ ^ 2) ^ 2 - (2 * b - 1) * m₀ ^ 2 + b = 0) :
    NodeCollisionFree (X - 1) (twistPolyNeg b) extraFactor m₀ 1 := by
  obtain ⟨h0, h1, -⟩ := twNeg_abNode_facts b hb hab
  have hx0 : m₀ ^ 2 ≠ 0 := pow_ne_zero 2 h0
  refine ⟨fun l hG _ ↦ ?_, fun l hT ↦ ?_⟩
  · rw [evalIntPoint_X_sub_one_twfNegAbCollision] at hG
    linear_combination hG
  rw [evalIntPoint_extraFactor] at hT
  refine ⟨?_, twistPolyNeg_ne_zero_of_extraFactor_abNode b hb hab h0 h1 hT, ?_⟩
  · rw [evalIntPoint_X_sub_one_twfNegAbCollision]
    intro h
    have hl : l = 1 := by linear_combination h
    rw [hl] at hT
    exact mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hx0 (by linear_combination hT)
  · rw [evalIntPoint_derivative_extraFactor]
    intro h
    have hsq : (l - m₀ ^ 2) * (l + m₀ ^ 2) = 0 := by
      linear_combination -hT + l * h
    rcases mul_eq_zero.1 hsq with h' | h'
    · have hq : (m₀ ^ 2) ^ 2 - 6 * m₀ ^ 2 + 1 = 0 := by linear_combination 2 * h' - h
      have : (4 * (b : ℂ) + 1) * m₀ ^ 2 = 0 := by linear_combination hab - (b : ℂ) * hq
      rcases mul_eq_zero.1 this with h4 | h4
      · have h4' : ((4 * b + 1 : ℕ) : ℂ) = 0 := by
          push_cast
          linear_combination h4
        exact absurd (Nat.cast_eq_zero.1 h4') (by omega)
      · exact hx0 h4
    · have : (m₀ ^ 2 - 1) ^ 2 = 0 := by linear_combination 2 * h' - h
      exact h1 (by linear_combination pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this)

end AJConjecture
