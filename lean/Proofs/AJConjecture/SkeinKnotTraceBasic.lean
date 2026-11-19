import Mathlib
import AJConjecture.SkeinBracketTrace
import AJConjecture.SkeinLongKnot
import AJConjecture.SkeinPlaceBasic
import AJConjecture.SkeinPtrTailBasic

/-!
# The knot trace through the long knot

`Tr_{K,k}(Y) = qtr_k(Λ_K(k) Y)` (the partial trace is a module map over the first bundle), and
`Tr_{K,k}(1)` is the bracket of the `k`-cable.
-/

namespace AJConjecture

/-- The knot trace is the quantum trace against the long knot. -/
theorem knotTrace_eq_qtr_longKnotOp (K : BraidKnot) (k : ℕ) (Y : SkMat k k) :
    knotTrace K k Y = qtr k (longKnotOp K k * Y) := by
  have hk : k ≤ k * K.strands := Nat.le_mul_of_pos_right k K.strands_pos
  rw [knotTrace, longKnotOp, qtr_eq_qtr_ptrTail k (k * K.strands) hk, ptrTail_mul_skPlace k _ hk]

/-- The knot trace of the identity is the bracket of the cable. -/
theorem knotTrace_one (K : BraidKnot) (k : ℕ) :
    knotTrace K k 1 = laurentToField (bracket (k * K.strands) (cable k K.word)) := by
  have hk : 0 + k ≤ k * K.strands := by
    rw [Nat.zero_add]
    exact Nat.le_mul_of_pos_right k K.strands_pos
  rw [knotTrace, skPlace_one _ 0 k hk, mul_one, laurentToField_bracket]

end AJConjecture
