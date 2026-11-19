import Mathlib
import AJConjecture.SkeinLongKnotCap
import AJConjecture.SkeinThickCupInner

/-!
# The long knot is natural with respect to nests of caps

A nest of `m` caps on `2m` adjacent strands of the cable can be pushed once around the knot:
`caps · Λ_K(k) = Λ_K(k + 2m) · caps`. Induction on `m`: the nest of `m + 1` caps is its innermost
cap
followed by the nest of `m` caps (`AJConjecture.capThick_succ_inner`, placed with
`AJConjecture.skPlace_mul` and `AJConjecture.skPlace_skPlace`), and one cap is
`AJConjecture.capAt_mul_longKnotOp`. The size `N = k + 2m` of the larger cable is a free parameter,
so that the statement applies to sizes written as `2 * (n + m)`.
-/

namespace AJConjecture

/-- The long knot is natural with respect to a nest of `m` caps, the larger size being free. -/
private theorem capThick_mul_longKnotOp_longKnotNest (K : BraidKnot) (m : ℕ) :
    ∀ N k i : ℕ, N = k + 2 * m → i ≤ k →
      skPlace N k i (capThick m) * longKnotOp K k =
        longKnotOp K N * skPlace N k i (capThick m) := by
  induction m with
  | zero =>
    intro N k i hN hi
    obtain rfl : N = k := by omega
    rw [capThick_zero, skPlace_one N i 0 (by omega), Matrix.one_mul, Matrix.mul_one]
  | succ m ih =>
    intro N k i hN hi
    obtain rfl : N = k + 2 * m + 2 := by omega
    have hsplit : skPlace (k + 2 * m + 2) k i (capThick (m + 1)) =
        capAt (k + 2 * m) (i + m) * skPlace (k + 2 * m) k i (capThick m) := by
      rw [capThick_succ_inner, skPlace_mul (k + 2 * m + 2) (k + 2 * m) k i _ _ (by omega)
        (by omega) (by omega), skPlace_skPlace (k + 2 * m + 2) (k + 2 * m) i m skCap (by omega)
        (by omega) (by omega) (by omega)]
      rfl
    rw [hsplit, Matrix.mul_assoc, ih (k + 2 * m) k i rfl hi, ← Matrix.mul_assoc,
      capAt_mul_longKnotOp K (k + 2 * m) (i + m) (by omega), Matrix.mul_assoc]

/-- The long knot is natural with respect to a nest of `m` caps at the position `i`. -/
theorem capThick_mul_longKnotOp (K : BraidKnot) (N k i m : ℕ) (hN : N = k + 2 * m) (hi : i ≤ k) :
    skPlace N k i (capThick m) * longKnotOp K k = longKnotOp K N * skPlace N k i (capThick m) :=
  capThick_mul_longKnotOp_longKnotNest K m N k i hN hi

end AJConjecture
