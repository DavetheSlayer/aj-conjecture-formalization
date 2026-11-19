import Mathlib
import AJFamily.Quantum.NodeCollision
import AJFamily.Quantum.EbNodeCollision
import AJTwist.Factor.TwFBlocksPullback
import AJTwist.Factor.TwFNegSymbolValues
import AJTwist.Factor.TwFNegEval

/-!
# The crossing `(L - 1)/C_b`: transversality (TwF, unit F2)

Source: revision 5, Section 5.2 (`operators.tex`, "The nodes and the physical first jet"): the
intersection of the varying block with `L - 1` has `J = 1`, `K = 2 + 1/a`, `Z = 2`; "At `J = 1`
the value `Z = 2` separates `L - 1` from `E`"; "Each entire meridian fiber has only the indicated
meeting of distinct blocks". Section 5.4: `H_J = -2(4b - 1)(b + 1)/(3b)`, `H_K = 4b` at the node.

At `(m₀, 1)` with `x₀ = m₀²`, `b x₀² - (2b - 1) x₀ + b = 0` (`K = 2 - 1/b`):
* `twNeg_abNode_facts`: `m₀ ≠ 0`, `m₀² ≠ ± 1`, `C_b = 0`, `E ≠ 0`, `∂_L C_b ≠ 0`, `∂_M C_b ≠ 0`
  (so the crossing with `L - 1` is simple and transversal: the Jacobian is `∂_M C_b`).
The fibre condition is in `AJTwist/Factor/TwFNegAbCollision.lean`.

Route. `E(M, 1) = 4 M²`. `C_b` is the pullback of `T̂_(-b)` (`twfPullback_symbolTwistNeg`,
`natDegree_symbolTwistNeg_le`); at `J = 1` the recursion has the double root `w = x₀`, and
`symbolTwistNeg_node_values`, `dblRootDeriv_mul_of_crit` give
`T̂_(-b) = x₀^(b-1) (x₀ + b (x₀ - 1)²)`, `∂_x T̂_(-b) = b (x₀² - 1) x₀^(b-2)` and
`∂_J T̂_(-b) = b x₀^b (K - 3)(K + 2)/6 = -(b + 1)(4b - 1) x₀^b/(6b)` on the node quadratic
(`K = x₀ + 1/x₀ = 2 - 1/b`; this is the paper's `H_J`, `H = (Z + 2) T_(-b)`), all nonzero; then
`evalIntPoint_derivative_twfPullback`,
`evalIntPoint_coeffDerivative_twfPullback` at `l = 1`, `J = 1`.
Checked for `b ≤ 6` modulo a prime (scratch `check_node_facts.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- At the abelian node, in the coordinates `(x, J)`: `T̂_(-b)` vanishes and both its first
derivatives are nonzero. -/
private theorem symbolTwistNeg_abNode_twfNegAbFacts (b : ℕ) (hb : 1 ≤ b) {x : ℂ}
    (hab : (b : ℂ) * x ^ 2 - (2 * b - 1) * x + b = 0) :
    evalIntPoint (symbolTwistNeg b) x 1 = 0 ∧
      evalIntPoint (derivative (symbolTwistNeg b)) x 1 ≠ 0 ∧
      evalIntPoint (coeffDerivative (symbolTwistNeg b)) x 1 ≠ 0 := by
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hb1 : (b : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : b + 1 ≠ 0)
  have h4b : 4 * (b : ℂ) - 1 ≠ 0 := by
    intro h
    have h4 : ((4 * b : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
      push_cast
      linear_combination h
    have := Nat.cast_injective h4
    omega
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb0 (by linear_combination hab)
  have hζ : evalIntPoint symbolZeta x 1 = 2 * x := by
    rw [evalIntPoint_symbolZeta]
    ring
  obtain ⟨hT, hTJ, hTx⟩ := symbolTwistNeg_node_values hζ rfl hx0 b
  have hcrit : x + b * (x ^ 2 + 1 - x * 1 - x) = 0 := by linear_combination hab
  have hDJ := dblRootDeriv_mul_of_crit (z₁ := -x) (α := 2 * x * 1 - (x ^ 2 + 1)) (β := 0) hb hx0
    hcrit
  have hDx := dblRootDeriv_mul_of_crit (z₁ := 2 * x - 1) (α := 1 ^ 2 - 2 * x * 1 + 2 * x + 1)
    (β := 2 * x) hb hx0 hcrit
  rw [← hTJ] at hDJ
  rw [← hTx] at hDx
  have hpow : x ^ (b - 1) ≠ 0 := pow_ne_zero _ hx0
  refine ⟨?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [hT]
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    linear_combination x ^ n * hcrit
  · rw [h, mul_zero] at hDJ
    have h0 := (mul_eq_zero.1 hDJ.symm).resolve_left hpow
    have h3 : x ^ 2 * ((4 * (b : ℂ) - 1) * (b + 1)) = 0 := by
      linear_combination -(b : ℂ) * h0 - ((b : ℂ) - 1) * (2 * b - 1) * x * hab
    exact mul_ne_zero (pow_ne_zero 2 hx0) (mul_ne_zero h4b hb1) h3
  · rw [h, mul_zero] at hDx
    have h0 := (mul_eq_zero.1 hDx.symm).resolve_left hpow
    have h3 : 2 * (b : ℂ) * x = 2 * b - 1 := by
      refine mul_left_cancel₀ (mul_ne_zero (show (6 : ℂ) ≠ 0 by norm_num) hx0) ?_
      linear_combination h0
    exact h4b (by linear_combination 4 * (b : ℂ) * hab - (2 * b * x - (2 * b - 1)) * h3)

/-- The values and derivatives at the abelian node of `P_(-b)` used by the index criterion. -/
theorem twNeg_abNode_facts (b : ℕ) (hb : 1 ≤ b) {m₀ : ℂ}
    (hab : (b : ℂ) * (m₀ ^ 2) ^ 2 - (2 * b - 1) * m₀ ^ 2 + b = 0) :
    m₀ ≠ 0 ∧ m₀ ^ 2 ≠ 1 ∧ m₀ ^ 2 ≠ -1 ∧
      evalIntPoint (twistPolyNeg b) m₀ 1 = 0 ∧ evalIntPoint extraFactor m₀ 1 ≠ 0 ∧
      evalIntPoint (derivative (twistPolyNeg b)) m₀ 1 ≠ 0 ∧
      evalIntPoint (coeffDerivative (twistPolyNeg b)) m₀ 1 ≠ 0 := by
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hx0 : m₀ ^ 2 ≠ 0 := by
    intro h
    rw [h] at hab
    exact hb0 (by linear_combination hab)
  have hm0 : m₀ ≠ 0 := fun h ↦ hx0 (by rw [h]; ring)
  have h1 : m₀ ^ 2 ≠ 1 := by
    intro h
    rw [h] at hab
    exact one_ne_zero (α := ℂ) (by linear_combination hab)
  have h2 : m₀ ^ 2 ≠ -1 := by
    intro h
    rw [h] at hab
    have h4 : ((4 * b : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
      push_cast
      linear_combination hab
    have := Nat.cast_injective h4
    omega
  have hs : (1 : ℂ) + m₀ ^ 2 ≠ 0 := fun h ↦ h2 (by linear_combination h)
  have hx2 : (m₀ ^ 2) ^ 2 - 1 ≠ 0 := by
    intro h
    have h' : (m₀ ^ 2 - 1) * (1 + m₀ ^ 2) = 0 := by linear_combination h
    exact mul_ne_zero (sub_ne_zero.2 h1) hs h'
  obtain ⟨hT0, hTJ, hTx⟩ := symbolTwistNeg_abNode_twfNegAbFacts b hb hab
  have hJ : (1 : ℂ) * (1 + m₀ ^ 2) = m₀ ^ 2 * 1 + 1 := by ring
  have hdeg := natDegree_symbolTwistNeg_le b hb
  have hval := evalIntPoint_twfPullback (2 * b - 1) _ hdeg hJ
  have hdL := evalIntPoint_derivative_twfPullback (2 * b - 1) _ hdeg hJ hT0
  have hdM := evalIntPoint_coeffDerivative_twfPullback (2 * b - 1) _ hdeg hJ hT0
  rw [twfPullback_symbolTwistNeg] at hval hdL hdM
  refine ⟨hm0, h1, h2, ?_, ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [hval, hT0, mul_zero]
  · rw [evalIntPoint_extraFactor]
    intro h
    exact mul_ne_zero (show (4 : ℂ) ≠ 0 by norm_num) hx0 (by linear_combination h)
  · rw [h, mul_zero] at hdL
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hs) hx2) hTJ hdL.symm
  · rw [h, mul_zero] at hdM
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hm0) (pow_ne_zero (2 * b - 1) hs))
      (mul_ne_zero (pow_ne_zero 2 hs) hTx) ?_
    linear_combination -hdM

end AJConjecture
