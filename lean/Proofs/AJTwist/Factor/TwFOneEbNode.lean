import Mathlib
import AJFamily.Quantum.NodeCollision
import AJFamily.Quantum.NodeClosedForms
import AJFamily.Quantum.TwistPolyBasic
import AJConjecture.WitnessPolynomials
import AJFamily.Quantum.EbNodeCollision

/-!
# The crossing `E/B_1`: transversality (TwF, unit F3)

Source: revision 5, Section 5.3 (`operators.tex`), "The `E/B_a` crossing": "For `a ≥ 1` … The
product and slope difference are nonzero. … In particular at `a = 1` the derivative product is
`160/351` … and the same simple crossing binds `E` to `B_1`"; eq. (enode) at `a = 1`:
`J = -1/3`, `K = -7/3`, `Z = -2`.

The library's `ebNode_facts`, `ebNode_collisionFree` (`AJFamily/Quantum/EbNodeFacts.lean`,
`EbNodeCollision.lean`) are stated for `m ≥ 2` and proved through closed forms that divide by
`m - 1`-type quantities and use `w^(m-2)`; at `m = 1` everything is explicit:
`B_1 = M⁴ L² - (M⁸ - M⁶ - 2M⁴ - M² + 1) L + M⁴` (`twistPoly_one_eq_explicit`),
`E = L² - (M⁴ - 4M² + 1) L + M⁴`, the node is `(m₀, l₀)` with `x₀ = m₀²`,
`3 x₀² + 7 x₀ + 3 = 0`, `J₀ = ebNodeJ 1 = -1/3`, `l₀ = ebNodeL 1 m₀ = (3 + x₀)/(-1 - 3 x₀)`.

* `famOne_ebNode_facts`: the twelve facts of `ebNode_facts` at `m = 1`.
The fibre condition is in `AJTwist/Factor/TwFOneEbCollision.lean`.

Route: direct computation modulo the node quadratic (`evalIntPoint` of explicit polynomials,
`field_simp`, `linear_combination … * heb`).
Checked modulo a prime (scratch `check_node_facts.py`, `a = 1`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `(L - 1)(m, l) = l - 1`. -/
private theorem evalIntPoint_X_sub_one_twfOneEbNode (m l : ℂ) :
    evalIntPoint (X - 1) m l = l - 1 := by
  simp [evalIntPoint, evalPoint]

/-- `J₀ = -1/3` at the `E/B_1` node. -/
private theorem ebNodeJ_one_twfOneEbNode : ebNodeJ 1 = -1 / 3 := by
  rw [ebNodeJ]
  norm_num

/-- `l₀ = 5 + (8/3) x₀` at the `E/B_1` node. -/
private theorem ebNodeL_one_twfOneEbNode {m₀ : ℂ} (heb : 3 * (m₀ ^ 2) ^ 2 + 7 * m₀ ^ 2 + 3 = 0) :
    ebNodeL 1 m₀ = 5 + 8 / 3 * m₀ ^ 2 := by
  have hden : (-1 / 3 : ℂ) - m₀ ^ 2 ≠ 0 := by
    intro h
    have h' : (1 : ℂ) = 0 := by linear_combination heb + (3 * m₀ ^ 2 + 6) * h
    norm_num at h'
  rw [ebNodeL, famNodeL, ebNodeJ_one_twfOneEbNode, div_eq_iff hden]
  linear_combination (8 / 9 : ℂ) * heb

/-- The values and derivatives at the `E/B_1` node used by the index criterion. -/
theorem famOne_ebNode_facts {m₀ : ℂ} (heb : 3 * (m₀ ^ 2) ^ 2 + 7 * m₀ ^ 2 + 3 = 0) :
    m₀ ≠ 0 ∧ m₀ ^ 2 ≠ 1 ∧ m₀ ^ 2 ≠ -1 ∧ m₀ ^ 2 ≠ ebNodeJ 1 ∧ m₀ ^ 2 * ebNodeJ 1 ≠ 1 ∧
      ebNodeL 1 m₀ ≠ 0 ∧ evalIntPoint (X - 1) m₀ (ebNodeL 1 m₀) ≠ 0 ∧
      evalIntPoint extraFactor m₀ (ebNodeL 1 m₀) = 0 ∧
      evalIntPoint (twistPoly 1) m₀ (ebNodeL 1 m₀) = 0 ∧
      evalIntPoint (derivative extraFactor) m₀ (ebNodeL 1 m₀) ≠ 0 ∧
      evalIntPoint (derivative (twistPoly 1)) m₀ (ebNodeL 1 m₀) ≠ 0 ∧
      evalIntPoint (derivative extraFactor) m₀ (ebNodeL 1 m₀) *
          evalIntPoint (coeffDerivative (twistPoly 1)) m₀ (ebNodeL 1 m₀) -
        evalIntPoint (coeffDerivative extraFactor) m₀ (ebNodeL 1 m₀) *
          evalIntPoint (derivative (twistPoly 1)) m₀ (ebNodeL 1 m₀) ≠ 0 := by
  have hm0 : m₀ ≠ 0 := by
    rintro rfl
    norm_num at heb
  rw [ebNodeL_one_twfOneEbNode heb, ebNodeJ_one_twfOneEbNode, evalIntPoint_X_sub_one_twfOneEbNode,
    evalIntPoint_extraFactor, evalIntPoint_twistPoly_one, evalIntPoint_derivative_extraFactor,
    evalIntPoint_derivative_twistPoly_one, evalIntPoint_coeffDerivative_extraFactor,
    evalIntPoint_coeffDerivative_twistPoly_one]
  refine ⟨hm0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h] at heb
    norm_num at heb
  · intro h
    rw [h] at heb
    norm_num at heb
  · intro h
    rw [h] at heb
    norm_num at heb
  · intro h
    have h' : m₀ ^ 2 = -3 := by linear_combination (-3 : ℂ) * h
    rw [h'] at heb
    norm_num at heb
  · intro h
    have h' : (3 : ℂ) = 0 := by
      linear_combination (-8 * (m₀ ^ 2) - 11 / 3) * h + (64 / 9) * heb
    norm_num at h'
  · intro h
    have h' : (-16 / 3 : ℂ) = 0 := by
      linear_combination (-8 * (m₀ ^ 2) - 20 / 3) * h + (64 / 9) * heb
    norm_num at h'
  · linear_combination (20 / 3 - 8 * (m₀ ^ 2) / 9) * heb
  · linear_combination (-8 * (m₀ ^ 2) ^ 3 / 9 + 11 * (m₀ ^ 2) ^ 2 / 3 + 14 * (m₀ ^ 2) / 3 -
      5 / 3) * heb
  · intro h
    have h' : (-325 / 3 : ℂ) = 0 := by
      linear_combination (-35 * (m₀ ^ 2) - 155 / 3) * h + (1070 / 9 - 35 * (m₀ ^ 2) / 3) * heb
    norm_num at h'
  · intro h
    have h' : (-832 / 27 : ℂ) = 0 := by
      linear_combination (-248 * (m₀ ^ 2) / 9 - 1232 / 27) * h +
        (-248 * (m₀ ^ 2) ^ 3 / 27 + 5216 * (m₀ ^ 2) ^ 2 / 81 + 1768 * (m₀ ^ 2) / 27 -
          688 / 27) * heb
    norm_num at h'
  · intro h
    have h' : (114244 / 3 : ℂ) * m₀ = 0 := by
      linear_combination (1690 * (m₀ ^ 2) / 27 - 21632 / 81) * h +
        m₀ * (-54080 * (m₀ ^ 2) ^ 5 / 243 + 1019408 * (m₀ ^ 2) ^ 4 / 243 -
          38406940 * (m₀ ^ 2) ^ 3 / 2187 - 599612 * (m₀ ^ 2) ^ 2 / 729 +
          47772920 * (m₀ ^ 2) / 729 + 5896748 / 243) * heb
    exact mul_ne_zero (by norm_num) hm0 h'

end AJConjecture
