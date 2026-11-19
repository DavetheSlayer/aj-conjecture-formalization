import Mathlib
import AJConjecture.SkeinMat

/-!
# The trace pairing is non-degenerate

`qtr(Z G) = ∑_{a,b} μ(a) Z a b · G b a`, and the weights `μ(a)` are units of `ℚ(t)`: testing
against the matrix units `G` shows that `Z` is determined by the functional `G ↦ qtr(Z G)`. This
turns an identity between traces, valid for every inserted matrix, into an identity between
operators.
-/

namespace AJConjecture

/-- The weight of a tensor factor is not zero. -/
private theorem skWeightEntry_ne_zero_tracePairing (b : Bool) : skWeightEntry b ≠ 0 := by
  cases b <;> simp [skWeightEntry, RatFunc.X_ne_zero]

/-- The quantum trace against a matrix unit is a weighted entry. -/
private theorem qtr_mul_single_tracePairing (n n' : ℕ) (Y : SkMat n n') (a : Fin n → Bool)
    (b : Fin n' → Bool) :
    qtr n (Y * Matrix.single b a (1 : RatFunc ℚ)) = (∏ k, skWeightEntry (a k)) * Y a b := by
  rw [qtr, ← Matrix.mul_assoc, Matrix.trace_mul_single, skWeight, Matrix.diagonal_mul,
    MulOpposite.op_one, one_smul]

/-- A rectangular matrix is determined by its trace pairing with all matrices. -/
theorem eq_of_forall_qtr_mul_eq (n n' : ℕ) (Z Z' : SkMat n n')
    (h : ∀ G : SkMat n' n, qtr n (Z * G) = qtr n (Z' * G)) : Z = Z' := by
  ext a b
  have hw : (∏ k, skWeightEntry (a k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ skWeightEntry_ne_zero_tracePairing (a k)
  have hab := h (Matrix.single b a (1 : RatFunc ℚ))
  rw [qtr_mul_single_tracePairing, qtr_mul_single_tracePairing] at hab
  exact mul_left_cancel₀ hw hab

end AJConjecture
