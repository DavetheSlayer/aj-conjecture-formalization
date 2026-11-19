import Mathlib
import AJConjecture.QAlgOreMulZero
import AJConjecture.QAlgOreResidueShift

/-!
# Left multiples of a monic operator have residue class `0`

Induction on `S`: additivity; for `S = C a * X^i`, `(C a * X^(i+1)) ⋆ R = C a * (X ⋆ (X^i ⋆ R))`
(`oreMul_assoc`, `C_mul_oreMul`), and `oreResidueClass_oreMul_X` maps the class `0` to
`C_R τ(0) = 0`; the base case is `oreResidueClass_self`.
-/

open Polynomial

namespace AJConjecture

/-- The left multiple `L^i ⋆ R` of a monic operator `R` has residue class `0` modulo `R`. -/
private theorem oreResidueClass_oreMul_X_pow {A : Type*} [CommRing A] (τ : A →+* A) {R : A[X]}
    (hR : R.Monic) (i : ℕ) : oreResidueClass τ R (oreMul τ (X ^ i) R) = 0 := by
  induction i with
  | zero => rw [pow_zero, oreMul_one_left, oreResidueClass_self τ hR]
  | succ i ih =>
    have hX : (X : A[X]) ^ (i + 1) = oreMul τ X (X ^ i) := by
      rw [Polynomial.X_pow_eq_monomial, Polynomial.X_pow_eq_monomial,
        ← Polynomial.monomial_one_one_eq_X, oreMul_monomial_monomial, Function.iterate_one,
        map_one τ, mul_one, add_comm]
    rw [hX, oreMul_assoc, oreResidueClass_oreMul_X, ih]
    funext k
    simp [Matrix.mulVec, dotProduct]

/-- A left multiple `S ⋆ R` of a monic operator `R` has residue class `0` modulo `R`. -/
theorem oreResidueClass_oreMul {A : Type*} [CommRing A] (τ : A →+* A) {R : A[X]}
    (hR : R.Monic) (S : A[X]) : oreResidueClass τ R (oreMul τ S R) = 0 := by
  induction S using Polynomial.induction_on' with
  | add p q hp hq => rw [oreMul_add_left, oreResidueClass_add, hp, hq, add_zero]
  | monomial i a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, ← C_mul_oreMul, oreResidueClass_C_mul,
      oreResidueClass_oreMul_X_pow τ hR, smul_zero]

end AJConjecture
