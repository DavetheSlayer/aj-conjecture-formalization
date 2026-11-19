import Mathlib
import AJConjecture.QAlgCoeffShiftBasic
import AJConjecture.QAlgOreMulBasic

/-!
# The specialisation at `t = -1` is multiplicative on Ore products

At `t = -1` the twist `M ↦ t² M` is the identity, so `specialize` sends the Ore product of
recurrence operators to the commutative product of `ℤ[M][L]`. This is the symbol lemma (Gauss
valuation at `t = -1` is additive on Ore products) in its polynomial form.
-/

open Polynomial

namespace AJConjecture

/-- The iterated shift is the identity after the specialisation `t = -1`. -/
theorem map_evalRingHom_iterate_coeffShift (i : ℕ) (c : Coeff) :
    (coeffShift^[i] c).map (Polynomial.evalRingHom (-1 : ℤ)) =
      c.map (Polynomial.evalRingHom (-1 : ℤ)) := by
  induction i generalizing c with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, ih, map_evalRingHom_coeffShift]

/-- The specialisation at `t = -1` sends Ore products to products. -/
theorem specialize_oreMul (P Q : RecOp) :
    specialize (oreMul coeffShift P Q) = specialize P * specialize Q := by
  induction P using Polynomial.induction_on' with
  | add p p' hp hp' => rw [oreMul_add_left, map_add, map_add, hp, hp', add_mul]
  | monomial i a =>
    induction Q using Polynomial.induction_on' with
    | add q q' hq hq' => rw [oreMul_add_right, map_add, map_add, hq, hq', mul_add]
    | monomial k b =>
      rw [oreMul_monomial_monomial]
      simp only [specialize, coe_mapRingHom, Polynomial.map_monomial, Polynomial.map_mul,
        map_evalRingHom_iterate_coeffShift, Polynomial.monomial_mul_monomial]

end AJConjecture
