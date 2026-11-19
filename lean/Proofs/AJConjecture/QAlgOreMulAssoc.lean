import Mathlib
import AJConjecture.QAlgOreMulBasic

/-!
# The Ore product is associative

On monomials both bracketings give `a σ^i(b) σ^(i+k)(c) X^(i+k+l)`; the general case follows by
additivity in each argument.
-/

open Polynomial

namespace AJConjecture

/-- The Ore product is associative on monomials. -/
private theorem oreMul_assoc_monomial {A : Type*} [Semiring A] (σ : A →+* A) (i k l : ℕ)
    (a b c : A) :
    oreMul σ (oreMul σ (monomial i a) (monomial k b)) (monomial l c) =
      oreMul σ (monomial i a) (oreMul σ (monomial k b) (monomial l c)) := by
  rw [oreMul_monomial_monomial, oreMul_monomial_monomial, oreMul_monomial_monomial,
    oreMul_monomial_monomial, iterate_map_mul, ← Function.iterate_add_apply, mul_assoc,
    add_assoc]

/-- The Ore product is associative. -/
theorem oreMul_assoc {A : Type*} [Semiring A] (σ : A →+* A) (P Q R : A[X]) :
    oreMul σ (oreMul σ P Q) R = oreMul σ P (oreMul σ Q R) := by
  induction P using Polynomial.induction_on' with
  | add p p' hp hp' => rw [oreMul_add_left, oreMul_add_left, oreMul_add_left, hp, hp']
  | monomial i a =>
    induction Q using Polynomial.induction_on' with
    | add q q' hq hq' =>
      rw [oreMul_add_right, oreMul_add_left, oreMul_add_left, oreMul_add_right, hq, hq']
    | monomial k b =>
      induction R using Polynomial.induction_on' with
      | add r r' hr hr' =>
        rw [oreMul_add_right, oreMul_add_right, oreMul_add_right, hr, hr']
      | monomial l c => exact oreMul_assoc_monomial σ i k l a b c

end AJConjecture
