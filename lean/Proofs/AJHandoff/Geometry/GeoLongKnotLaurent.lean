import Mathlib
import AJConjecture.SkeinLongKnot
import AJConjecture.FieldActionBridge

/-!
# The long knot has Laurent-polynomial entries

The braid matrices over `ℚ(t)` are the images of the integral braid matrices, and the weights
of the partial trace are `-t^{∓2}`, so every entry of the long knot `longKnotOp K k` lies in the
image of `ℤ[t, t⁻¹]` in `ℚ(t)`.
-/

namespace AJConjecture

/-- The braid matrix over `ℚ(t)` is the image of the braid matrix over `ℤ[t, t⁻¹]`. -/
theorem braidMatrix_eq_map_laurent (m : ℕ) (w : BraidWord) :
    braidMatrix m w = ((w.map (crossingMatrix m)).prod).map laurentToField := by
  rw [braidMatrix, ← RingHom.mapMatrix_apply, map_list_prod, List.map_map]
  rfl

/-- The entries of a braid matrix are Laurent polynomials. -/
theorem braidMatrix_apply_mem_range (m : ℕ) (w : BraidWord) (a b : Fin m → Bool) :
    braidMatrix m w a b ∈ laurentToField.range := by
  rw [braidMatrix_eq_map_laurent, Matrix.map_apply]
  exact RingHom.mem_range_self _ _

/-- The weight of one factor of the quantum trace is a Laurent polynomial. -/
theorem skWeightEntry_mem_range (b : Bool) : skWeightEntry b ∈ laurentToField.range := by
  cases b
  · exact ⟨-LaurentPolynomial.T 2, by
      simp only [map_neg, laurentToField_T, skWeightEntry, Bool.false_eq_true, ite_false]⟩
  · exact ⟨-LaurentPolynomial.T (-2), by
      simp only [map_neg, laurentToField_T, skWeightEntry, ite_true]⟩

/-- The partial trace of a matrix with Laurent-polynomial entries has Laurent-polynomial
entries. -/
theorem ptrTail_apply_mem_range (k n : ℕ) (A : SkMat n n)
    (hA : ∀ a b, A a b ∈ laurentToField.range) (a b : Fin k → Bool) :
    ptrTail k n A a b ∈ laurentToField.range := by
  rw [ptrTail, Matrix.of_apply]
  refine Subring.sum_mem _ fun s _ ↦ Subring.mul_mem _ ?_ (hA _ _)
  exact Subring.prod_mem _ fun x _ ↦ skWeightEntry_mem_range (s x)

/-- The entries of the long knot are Laurent polynomials. -/
theorem longKnotOp_apply_mem_range (K : BraidKnot) (k : ℕ) (a b : Fin k → Bool) :
    longKnotOp K k a b ∈ laurentToField.range :=
  ptrTail_apply_mem_range k _ _ (braidMatrix_apply_mem_range _ _) a b

end AJConjecture
