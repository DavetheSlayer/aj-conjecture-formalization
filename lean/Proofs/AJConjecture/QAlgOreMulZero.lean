import Mathlib
import AJConjecture.QAlgOreMulAssoc

/-!
# The Ore product: zero and constant multiples

Small rules used throughout: the Ore product with `0` on either side is `0`, and multiplying
an Ore product on the left by a constant multiplies its left factor.
-/

open Polynomial

namespace AJConjecture

/-- The Ore product with `0` on the left is `0`. -/
theorem oreMul_zero_left {A : Type*} [Semiring A] (σ : A →+* A) (Q : A[X]) :
    oreMul σ 0 Q = 0 := by
  simp [oreMul]

/-- The Ore product with `0` on the right is `0`. -/
theorem oreMul_zero_right {A : Type*} [Semiring A] (σ : A →+* A) (P : A[X]) :
    oreMul σ P 0 = 0 := by
  simp [oreMul, Polynomial.sum_def]

/-- A constant on the left can be moved into the left factor of an Ore product. -/
theorem C_mul_oreMul {A : Type*} [Semiring A] (σ : A →+* A) (c : A) (P Q : A[X]) :
    C c * oreMul σ P Q = oreMul σ (C c * P) Q := by
  rw [← oreMul_C_left σ c (oreMul σ P Q), ← oreMul_C_left σ c P, oreMul_assoc]

end AJConjecture
