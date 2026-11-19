import Mathlib
import AJTwist.Factor.TwFTargetBridge
import AJTwist.Factor.TwFNegEbCert

/-!
# The crossing `E/C_b`: the Weyl symbol vanishes (TwF, unit F2)

Source: revision 5, Section 5.4 (`operators.tex`): at the crossing `E/C_b` both indices are
`-1/2` (`κ = (s_G + s_H)/2`).

`evalIntPoint_weylSymbol_twTransferOp_neg_ebNode`: the Weyl subprincipal symbol of `P_(-b)`
vanishes at the node `(m₀, twNegNodeL b m₀)`.

Route: `evalIntPoint_weylSymbol_twTransferOp_eq_zero` with `a = -b`, `J₀ = twNegNodeJ b`
(`twNegNodeL b m₀ = famNodeL m₀² J₀` by definition), `twTarget_neg_natCast`,
`twWindow_neg_natCast`; `hpJ`, `hpx` from `twNegTarget_one_derivatives_ebNode` and
`twNeg_ebNode_zeta`; `htarget` from `evalEval_twNegTarget_dual_node` with `w = -m₀²` (the value
condition `w² + x₀ w (1 - J₀) - x₀² J₀ = 0` holds identically for `w = -x₀`; `hw` is
`twNeg_ebNode_zeta` since `twJetZeta d 1 x j = ζ(x, j)`); `hcert` is `twNeg_ebNode_cert`. The
conditions `m₀² ≠ ± 1`, `m₀² ≠ J₀`, `m₀² J₀ ≠ 1` follow from the node quadratic (values
`8b² - 4b + 1`, `-1` at `x = ± 1`; `J₀` and `1/J₀` are not roots).
Checked directly from the definition of the operator for `1 ≤ b ≤ 7` (scratch `check_weyl.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The nondegeneracy of the `E/C_b` node in the coordinates `(x, J)`: `x₀ ≠ ± 1`, `x₀ ≠ J₀`,
`x₀ J₀ ≠ 1`. -/
private theorem twNeg_ebNode_ne_twfNegEbWeyl (b : ℕ) (hb : 1 ≤ b) {x : ℂ}
    (heb : (b : ℂ) * (2 * b - 1) * x ^ 2 + (4 * b ^ 2 - 2 * b + 1) * x + b * (2 * b - 1) = 0) :
    x ≠ 1 ∧ x ≠ -1 ∧ x ≠ twNegNodeJ b ∧ x * twNegNodeJ b ≠ 1 := by
  have h2b : 2 * (b : ℂ) - 1 ≠ 0 := by
    intro h
    have h' : ((2 * b : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
      push_cast
      linear_combination h
    have := Nat.cast_injective h'
    omega
  have hJ : (2 * (b : ℂ) - 1) * twNegNodeJ b = -(2 * b + 1) := by
    rw [twNegNodeJ]
    field_simp
  generalize twNegNodeJ b = J at hJ ⊢
  have hP : (b : ℂ) * (2 * b - 1) * J ^ 2 + (4 * b ^ 2 - 2 * b + 1) * J + b * (2 * b - 1) = 1 := by
    refine mul_left_cancel₀ (pow_ne_zero 2 h2b) ?_
    linear_combination ((b : ℂ) * (2 * b - 1) * ((2 * b - 1) * J - (2 * b + 1)) +
      (4 * (b : ℂ) ^ 2 - 2 * b + 1) * (2 * b - 1)) * hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl
    have h8 : ((8 * b ^ 2 + 1 : ℕ) : ℂ) = ((4 * b : ℕ) : ℂ) := by
      push_cast
      linear_combination heb
    have h8' : 8 * b ^ 2 + 1 = 4 * b := Nat.cast_injective h8
    nlinarith
  · rintro rfl
    exact one_ne_zero (α := ℂ) (by linear_combination -heb)
  · rintro rfl
    exact one_ne_zero (α := ℂ) (by linear_combination heb - hP)
  · intro h
    refine one_ne_zero (α := ℂ) ?_
    linear_combination J ^ 2 * heb - hP -
      ((b : ℂ) * (2 * b - 1) * (x * J + 1) + (4 * (b : ℂ) ^ 2 - 2 * b + 1) * J) * h

/-- The Weyl subprincipal symbol of `P_(-b)` vanishes at the `E/C_b` node
`(m₀, twNegNodeL b m₀)`. -/
theorem evalIntPoint_weylSymbol_twTransferOp_neg_ebNode (b : ℕ) (hb : 1 ≤ b) {m₀ : ℂ}
    (heb : (b : ℂ) * (2 * b - 1) * (m₀ ^ 2) ^ 2 + (4 * b ^ 2 - 2 * b + 1) * m₀ ^ 2 +
      b * (2 * b - 1) = 0) :
    evalIntPoint (weylSymbol (twTransferOp (-(b : ℤ)))) m₀ (twNegNodeL b m₀) = 0 := by
  obtain ⟨h1, h2, hJ, hJ'⟩ := twNeg_ebNode_ne_twfNegEbWeyl b hb heb
  obtain ⟨hζ, hT0⟩ := twNeg_ebNode_zeta b hb heb
  obtain ⟨hpJ, hpx, -⟩ := twNegTarget_one_derivatives_ebNode b hb hζ hT0
  have key := evalIntPoint_weylSymbol_twTransferOp_eq_zero (-(b : ℤ)) (m₀ := m₀)
    (J₀ := twNegNodeJ b) (h₁ := twNegTargetJet b (m₀ ^ 2) (twNegNodeJ b) (-(m₀ ^ 2))) h1 h2 hJ hJ'
  rw [twTarget_neg_natCast b hb, twTarget_neg_natCast b hb, twWindow_neg_natCast b hb] at key
  refine key hpJ hpx (evalEval_twNegTarget_dual_node b hb ?_ (by ring) (by ring))
    (twNeg_ebNode_cert b hb heb)
  rw [← hζ, evalIntPoint_symbolZeta]
  simp only [twJetZeta]
  ring

end AJConjecture
