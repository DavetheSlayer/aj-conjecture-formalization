import Mathlib
import AJTwist.Classical.TwCPolys
import AJTwist.Quantum.TwQSymbol

/-!
# The classical filling polynomial is the quantum block

`twP k` (the classical `𝒫_k` of Section 7.2 of revision 5) is the varying block `twBlock k` of the
symbol of the operator `P_k` on the quantum side (`AJTwist.Quantum.TwQSymbol`, Section 3.4).
Both are `B_k = twistPoly k` for `k ≥ 1`, `1` for `k = 0` and `C_(-k) = twistPolyNeg (-k)` for
`k < 0`; the two definitions differ only in how the case `k = 0` is written. This is the
identification "the same trace polynomials control the classical fillings and the commuting
symbol" of the paper.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The classical filling polynomial is the block of the quantum symbol. -/
theorem twP_eq_twBlock (k : ℤ) : twP k = twBlock k := by
  unfold twP twBlock
  by_cases h1 : 1 ≤ k
  · rw [ite_eq_left (by omega), ite_eq_left h1]
  · by_cases h0 : k = 0
    · subst h0
      simp [twistPoly]
    · rw [ite_eq_right (by omega), ite_eq_right h1, ite_eq_right h0]

end AJConjecture
