import Mathlib
import AJTwist.Factor.TwFZeroEven
import AJTwist.Factor.TwFZeroInfinity

/-!
# `P_0` has no right factor of order one (TwF, unit F4)

Source: revision 5, Section 5.6 (`operators.tex`, "First-order right divisors at `a = 0`"):
"This contradiction excludes linear right factors over `ℚ(t, M)`. … With the nonzero sequence
class, this exclusion is enough for the selection in Section 6."

`natDegree_ne_one_of_oreMul_eq_twTransferOp_zero`: in every pseudo-factorisation
`β · twTransferOp 0 = S ⋆ R` the right factor does not have degree one. This is the shape the
selection package consumes (`tws_exists_selected_divisor_of_no_linear`).

Proof: the descent `twf_zero_exists_even_solution` (uniqueness, the involution `M ↦ -M`, the
first jet) and the nonexistence `twf_zero_no_solution` (normal form over `ℚ(t)[x]`, reduction at
`t = -1`, value at `x = 0`, limit at infinity).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The operator `P_0` has no right pseudo-factor of degree one. -/
theorem natDegree_ne_one_of_oreMul_eq_twTransferOp_zero {β : Coeff} (hβ : β ≠ 0)
    {S R : RecOp} (h : C β * twTransferOp 0 = oreMul coeffShift S R) : R.natDegree ≠ 1 := by
  intro hR
  obtain ⟨e₀, e₁, h₁, h₀₁, hric, hjet⟩ := twf_zero_exists_even_solution hβ h hR
  exact twf_zero_no_solution h₁ h₀₁ hric hjet

end AJConjecture
