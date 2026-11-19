import Mathlib
import AJFamily.Quantum.NodeCollision
import AJFamily.Quantum.NodeClosedForms
import AJFamily.Quantum.TwistPolyBasic
import AJConjecture.WitnessPolynomials
import AJFamily.Quantum.EbNodeCollision

import AJTwist.Factor.TwFOneEbNode

/-!
# The crossing `E/B_1`: the fibre (TwF, unit F3)

Source: revision 5, Section 5.2 (`operators.tex`): "Each entire meridian fiber has only the
indicated meeting of distinct blocks", at `a = 1`.

`famOne_ebNode_collisionFree`: on the fibre `M = m₀` of the `E/B_1` node
(`3 x₀² + 7 x₀ + 3 = 0`, `x₀ = m₀²`) the blocks `E` and `B_1` meet only at `l₀ = ebNodeL 1 m₀`,
and `L = 1` is a zero of neither.

Route: `E` and `B_1 = x₀² L² - (x₀⁴ - x₀³ - 2x₀² - x₀ + 1) L + x₀²` are explicit quadratics in
`L`; `x₀² E - B_1` is linear in `L` with nonzero leading coefficient on the node quadratic, so a
common zero is unique, and `l₀` is one (`famOne_ebNode_facts`). `E(m₀, 1) = 4 x₀`,
`B_1(m₀, 1) = -(x₀² - 3 x₀ + 1)(x₀ + 1)² ≠ 0` since `x₀² - 3x₀ + 1` and `3x₀² + 7x₀ + 3` have
no common root.
Checked modulo a prime (scratch `check_node_facts.py`, `a = 1`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `(L - 1)(m, l) = l - 1`. -/
private theorem evalIntPoint_X_sub_one_twfOneEbCollision (m l : ℂ) :
    evalIntPoint (X - 1) m l = l - 1 := by
  simp [evalIntPoint, evalPoint]

/-- The `E/B_1` node is collision free. -/
theorem famOne_ebNode_collisionFree {m₀ : ℂ} (heb : 3 * (m₀ ^ 2) ^ 2 + 7 * m₀ ^ 2 + 3 = 0) :
    NodeCollisionFree extraFactor (twistPoly 1) (X - 1) m₀ (ebNodeL 1 m₀) := by
  obtain ⟨hm0, h1, -, -, -, -, -, hE0, hB0, -, -, -⟩ := famOne_ebNode_facts heb
  have h3 : 3 * (m₀ ^ 2) ^ 2 - 1 ≠ 0 := by
    intro h
    have h' : (-1 : ℂ) = 0 := by
      linear_combination (21 * (m₀ ^ 2) + 37) * h + (12 - 21 * (m₀ ^ 2)) * heb
    norm_num at h'
  refine ⟨fun l hE hB ↦ ?_, fun l hl ↦ ?_⟩
  · rw [evalIntPoint_extraFactor] at hE hE0
    rw [evalIntPoint_twistPoly_one] at hB hB0
    have key : (m₀ ^ 2 - 1) * (3 * (m₀ ^ 2) ^ 2 - 1) * (l - ebNodeL 1 m₀) = 0 := by
      linear_combination (m₀ ^ 2) ^ 2 * hE - hB - (m₀ ^ 2) ^ 2 * hE0 + hB0
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp key).resolve_left (mul_ne_zero (sub_ne_zero.mpr h1) h3))
  · rw [evalIntPoint_X_sub_one_twfOneEbCollision] at hl
    obtain rfl : l = 1 := by linear_combination hl
    refine ⟨?_, ?_, ?_⟩
    · rw [evalIntPoint_extraFactor]
      intro h
      have h' : m₀ ^ 2 = 0 := by linear_combination h / 4
      exact hm0 (pow_eq_zero_iff two_ne_zero |>.mp h')
    · rw [evalIntPoint_twistPoly_one]
      intro h
      have h' : (256 / 27 : ℂ) = 0 := by
        linear_combination (-112 * (m₀ ^ 2) / 9 - 640 / 27) * h +
          (-112 * (m₀ ^ 2) ^ 3 / 27 + 160 * (m₀ ^ 2) ^ 2 / 27 + 400 * (m₀ ^ 2) / 27 -
            128 / 27) * heb
      norm_num at h'
    · rw [evalIntPoint_derivative_X_sub_one]
      exact one_ne_zero

end AJConjecture
