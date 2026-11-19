import Mathlib
import AJConjecture.FieldActionBridge
import AJConjecture.SkeinBracketTrace
import AJConjecture.SkeinBraidMatrixPlace
import AJConjecture.SkeinPtrTailBasic
import AJConjecture.SkeinPtrTailPlace
import AJConjecture.SkeinTraceCyclic

/-!
# The bracket is a Markov trace on words

Conjugation: `⟨closure of u v⟩ = ⟨closure of v u⟩`, because the weight commutes with the crossing
matrices. Stabilisation: adding a strand with one crossing multiplies the bracket by the kink
factor `-t^{±3}`; the partial trace of `σ_{m-1}^{±1}` over the new strand is `-t^{±3}`.
-/

open LaurentPolynomial

namespace AJConjecture

/-- The bracket is invariant under cyclic rotation of the braid word. -/
theorem bracket_append_comm (m : ℕ) (u v : BraidWord) :
    bracket m (u ++ v) = bracket m (v ++ u) := by
  apply laurentToField_injective
  rw [laurentToField_bracket, laurentToField_bracket, braidMatrix_append, braidMatrix_append]
  exact qtr_mul_comm_of_weight m m _ _ (skWeight_mul_braidMatrix m u)

/-- Markov stabilisation, with the number of strands written as `n + 1`. -/
private theorem qtr_braidMatrix_stabilise_succ_bracketCyclic (n : ℕ) (w : BraidWord) (s : Bool)
    (hw : IsOnStrands (n + 1) w) :
    qtr (n + 2) (braidMatrix (n + 2) (w ++ [(n, s)])) =
      (if s then -(RatFunc.X : RatFunc ℚ) ^ (3 : ℤ) else -(RatFunc.X : RatFunc ℚ) ^ (-3 : ℤ)) *
        qtr (n + 1) (braidMatrix (n + 1) w) := by
  have hplace : braidMatrix (n + 2) w = skPlace (n + 2) (n + 2) 0 (braidMatrix (n + 1) w) := by
    have key := braidMatrix_map_add_eq_skPlace (n + 1) (n + 2) 0 w hw (by omega)
    rwa [show (w.map fun g : ℕ × Bool ↦ (g.1 + 0, g.2)) = w from List.map_id w] at key
  have hsing : braidMatrix (n + 2) [(n, s)] = crossingF (n + 2) (n, s) := by
    rw [braidMatrix, List.map_cons, List.map_nil, List.prod_singleton]
  rw [braidMatrix_append, hsing, hplace, qtr_eq_qtr_ptrTail (n + 1) (n + 2) (by omega),
    ptrTail_skPlace_mul (n + 1) (n + 2) (by omega), ptrTail_crossingF_last, Matrix.mul_smul,
    Matrix.mul_one, qtr, qtr, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- Markov stabilisation for one strand: a kink contributes `-t³` (positive) or `-t⁻³`. -/
theorem qtr_braidMatrix_stabilise (m : ℕ) (w : BraidWord) (s : Bool) (hw : IsOnStrands m w)
    (hm : 0 < m) :
    qtr (m + 1) (braidMatrix (m + 1) (w ++ [(m - 1, s)])) =
      (if s then -(RatFunc.X : RatFunc ℚ) ^ (3 : ℤ) else -(RatFunc.X : RatFunc ℚ) ^ (-3 : ℤ)) *
        qtr m (braidMatrix m w) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact qtr_braidMatrix_stabilise_succ_bracketCyclic n w s hw

end AJConjecture
