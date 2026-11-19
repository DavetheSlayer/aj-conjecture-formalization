import Mathlib
import AJConjecture.FieldActionBridge
import AJConjecture.SkeinMat

/-!
# The bracket is a quantum trace over `ℚ(t)`

`laurentToField ⟨closure of w⟩ = qtr_m(ρ_m(w))`: the ring homomorphism `laurentToField` commutes
with the trace, with the product of the crossing matrices and with the diagonal weight
(`laurentToField (T n) = t^n`). This is the interface between the definitions of
`AJConjecture.bracket` and the field-valued calculus.
-/

open LaurentPolynomial

namespace AJConjecture

/-- The braid matrix is the image of the product of the crossing matrices. -/
private theorem braidMatrix_eq_mapMatrix_bracketTrace (m : ℕ) (w : BraidWord) :
    braidMatrix m w = laurentToField.mapMatrix (w.map (crossingMatrix m)).prod := by
  rw [map_list_prod, List.map_map]
  rfl

/-- The weight of the quantum trace is the image of the weight in the definition of the
bracket. -/
private theorem skWeight_eq_mapMatrix_bracketTrace (m : ℕ) :
    skWeight m = laurentToField.mapMatrix
      (Matrix.diagonal (fun a : Fin m → Bool ↦ ∏ k, if a k then -T (-2) else -T 2)) := by
  rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _), skWeight]
  congr 1
  funext a
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  unfold skWeightEntry
  split_ifs <;> rw [map_neg, laurentToField_T]

/-- The image of the Kauffman bracket of a closed braid in `ℚ(t)` is the quantum trace of its
braid matrix. -/
theorem laurentToField_bracket (m : ℕ) (w : BraidWord) :
    laurentToField (bracket m w) = qtr m (braidMatrix m w) := by
  rw [qtr, braidMatrix_eq_mapMatrix_bracketTrace, skWeight_eq_mapMatrix_bracketTrace, ← map_mul,
    bracket, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]

end AJConjecture
