import Mathlib
import AJConjecture.QAlgHomogenizeOp
import AJConjecture.QAlgOpApplyFieldOreMul
import AJConjecture.QAlgOreMulDegree

/-!
# The homogenised operator annihilates

`(homogenizeOp β δ P) f (n) = β(n) δ(n+1) (P f)(n+1) - β(n+1) δ(n) (P f)(n)`, which vanishes
as soon as `δ · (P f) = β` at the colours `n` and `n + 1`; no division is involved. Its degree
is one more than the degree of `P`.
-/

open Polynomial

namespace AJConjecture

/-- The action of the homogenised operator. -/
theorem opApplyField_homogenizeOp (β δ : Coeff) (P : RecOp) (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (homogenizeOp β δ P) f n =
      evalAtField n β * evalAtField (n + 1) δ * opApplyField P f (n + 1) -
        evalAtField (n + 1) β * evalAtField n δ * opApplyField P f n := by
  rw [homogenizeOp, opApplyField_oreMul, opApplyField_sub_left, C_mul_X_eq_monomial,
    ← monomial_zero_left, opApplyField_monomial, opApplyField_monomial, map_mul, map_mul,
    evalAtField_coeffShift, evalAtField_coeffShift, Nat.cast_one, Nat.cast_zero, add_zero]

/-- The homogenised operator annihilates `f` at `n` when `δ · (P f) = β` at `n` and `n + 1`. -/
theorem opApplyField_homogenizeOp_eq_zero {β δ : Coeff} {P : RecOp} {f : ℤ → RatFunc ℚ} {n : ℤ}
    (h0 : evalAtField n δ * opApplyField P f n = evalAtField n β)
    (h1 : evalAtField (n + 1) δ * opApplyField P f (n + 1) = evalAtField (n + 1) β) :
    opApplyField (homogenizeOp β δ P) f n = 0 := by
  rw [opApplyField_homogenizeOp, mul_assoc, h1, mul_assoc, h0, mul_comm, sub_self]

/-- The homogenised operator has degree one more than `P`. -/
theorem natDegree_homogenizeOp {β δ : Coeff} (hβ : β ≠ 0) (hδ : δ ≠ 0) {P : RecOp}
    (hP : P ≠ 0) : (homogenizeOp β δ P).natDegree = P.natDegree + 1 := by
  have ha : β * coeffShift δ ≠ 0 :=
    mul_ne_zero hβ ((map_ne_zero_iff _ coeffShift_injective).mpr hδ)
  have hdeg : (C (β * coeffShift δ) * X - C (coeffShift β * δ) : RecOp).natDegree = 1 := by
    rw [sub_eq_add_neg, ← C_neg]
    exact natDegree_linear ha
  have hne : (C (β * coeffShift δ) * X - C (coeffShift β * δ) : RecOp) ≠ 0 := fun h0 ↦ by
    rw [h0, natDegree_zero] at hdeg
    exact zero_ne_one hdeg
  rw [homogenizeOp, natDegree_oreMul coeffShift_injective hne hP, hdeg, add_comm]

end AJConjecture
