import Mathlib
import AJConjecture.QAlgInnerDerivative
import AJConjecture.QAlgWeylSymbol

/-!
# Rules for the derivative with respect to the inner variable

`innerDerivative` is additive, a derivation, differentiates constants of `A[M]`, commutes with
base change, and is `coeffDerivative` over `ℤ`. Proofs: `Polynomial.induction_on'` and
`Polynomial.sum_monomial_index`.
-/

open Polynomial

namespace AJConjecture

/-- The inner derivative is additive. -/
theorem innerDerivative_add {A : Type*} [CommSemiring A] (p q : A[X][X]) :
    innerDerivative (p + q) = innerDerivative p + innerDerivative q := by
  unfold innerDerivative
  refine Polynomial.sum_add_index p q _ (fun k ↦ ?_) (fun k a b ↦ ?_)
  · rw [derivative_zero, monomial_zero_right]
  · rw [derivative_add, map_add]

/-- The inner derivative of a monomial in the outer variable. -/
private theorem innerDerivative_monomial_innerDerivBasic {A : Type*} [CommSemiring A] (k : ℕ)
    (c : A[X]) : innerDerivative (monomial k c) = monomial k (derivative c) := by
  unfold innerDerivative
  rw [Polynomial.sum_monomial_index]
  rw [derivative_zero, monomial_zero_right]

/-- The Leibniz rule for the inner derivative. -/
theorem innerDerivative_mul {A : Type*} [CommSemiring A] (p q : A[X][X]) :
    innerDerivative (p * q) = innerDerivative p * q + p * innerDerivative q := by
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' =>
    rw [add_mul, innerDerivative_add, hp, hp', innerDerivative_add]
    ring
  | monomial i a =>
    induction q using Polynomial.induction_on' with
    | add q q' hq hq' =>
      rw [mul_add, innerDerivative_add, hq, hq', innerDerivative_add]
      ring
    | monomial k b =>
      rw [monomial_mul_monomial, innerDerivative_monomial_innerDerivBasic,
        innerDerivative_monomial_innerDerivBasic, innerDerivative_monomial_innerDerivBasic,
        monomial_mul_monomial, monomial_mul_monomial, ← map_add, derivative_mul]

/-- The inner derivative of a constant of `A[M]`. -/
theorem innerDerivative_C {A : Type*} [CommSemiring A] (c : A[X]) :
    innerDerivative (C c) = C (derivative c) := by
  rw [← monomial_zero_left, innerDerivative_monomial_innerDerivBasic, monomial_zero_left]

/-- The inner derivative commutes with base change. -/
theorem innerDerivative_map {A B : Type*} [CommSemiring A] [CommSemiring B] (f : A →+* B)
    (p : A[X][X]) :
    innerDerivative (p.map (Polynomial.mapRingHom f)) =
      (innerDerivative p).map (Polynomial.mapRingHom f) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.map_add, innerDerivative_add, hp, hq, innerDerivative_add, Polynomial.map_add]
  | monomial k c =>
    rw [map_monomial, innerDerivative_monomial_innerDerivBasic,
      innerDerivative_monomial_innerDerivBasic, map_monomial, coe_mapRingHom,
      derivative_map]

/-- Over `ℤ` the inner derivative is `coeffDerivative`. -/
theorem coeffDerivative_eq_innerDerivative (p : ℤ[X][X]) :
    coeffDerivative p = innerDerivative p :=
  rfl

end AJConjecture
