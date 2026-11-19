import Mathlib
import AJConjecture.QAlgCoeffShiftBasic
import AJConjecture.QAlgOpApplyFieldBasic
import AJConjecture.QAlgOreMulBasic

/-!
# The Ore product acts by composition

The action of recurrence operators on sequences is a left module structure for the Ore product
twisted by `M ↦ t² M`: `(P ⋆ Q) f = P (Q f)`, at every integer colour and without exceptional
colours, because the coefficients are polynomials in `M`.
-/

open Polynomial

namespace AJConjecture

/-- The Ore product of a monomial `a L ^ i` with an operator `Q` acts by `a` times the shift by
`i` of the action of `Q`. -/
private theorem opApplyField_monomial_oreMul (i : ℕ) (a : Coeff) (Q : RecOp) (f : ℤ → RatFunc ℚ)
    (n : ℤ) :
    opApplyField (oreMul coeffShift (monomial i a) Q) f n =
      evalAtField n a * opApplyField Q f (n + i) := by
  induction Q using Polynomial.induction_on' with
  | add Q Q' hQ hQ' =>
    rw [oreMul_add_right, opApplyField_add_left, opApplyField_add_left, hQ, hQ', mul_add]
  | monomial k b =>
    rw [oreMul_monomial_monomial, opApplyField_monomial, opApplyField_monomial, map_mul,
      evalAtField_iterate_coeffShift, mul_assoc, Nat.cast_add, add_assoc]

/-- The Ore product of recurrence operators acts on sequences by composition. -/
theorem opApplyField_oreMul (P Q : RecOp) (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (oreMul coeffShift P Q) f n =
      opApplyField P (fun m ↦ opApplyField Q f m) n := by
  induction P using Polynomial.induction_on' with
  | add P P' hP hP' =>
    rw [oreMul_add_left, opApplyField_add_left, opApplyField_add_left, hP, hP']
  | monomial i a =>
    rw [opApplyField_monomial_oreMul, opApplyField_monomial]

end AJConjecture
