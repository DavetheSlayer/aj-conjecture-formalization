import Mathlib
import AJConjecture.QAlgCoeffShift
import AJConjecture.WhiteheadFormula

/-!
# Basic properties of the coefficient shift

The shift `M ↦ t² M` is injective, shifts the colour by one under evaluation, and becomes the
identity after the specialisation `t = -1`.
-/

open Polynomial

namespace AJConjecture

/-- The coefficient shift is injective. -/
theorem coeffShift_injective : Function.Injective coeffShift := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  have hcomp : c.comp (C (X ^ 2) * X : Coeff) = 0 := hc
  rcases Polynomial.comp_eq_zero_iff.mp hcomp with h | ⟨-, h⟩
  · exact h
  · exfalso
    have h1 := congrArg (fun p : Coeff ↦ p.coeff 1) h
    simp only [coeff_C_mul, coeff_X_one, mul_one, coeff_C_succ] at h1
    exact pow_ne_zero 2 X_ne_zero h1

/-- Evaluating a shifted coefficient at the colour `n` is evaluating at the colour `n + 1`. -/
theorem evalAtField_coeffShift (n : ℤ) (c : Coeff) :
    evalAtField n (coeffShift c) = evalAtField (n + 1) c := by
  have hcomp : coeffShift c = c.comp (C (X ^ 2) * X : Coeff) := rfl
  rw [hcomp]
  simp only [evalAtField, coe_eval₂RingHom, eval₂_comp, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow]
  congr 1
  rw [← zpow_natCast, ← zpow_add₀ RatFunc.X_ne_zero]
  congr 1
  push_cast
  ring

/-- Evaluating an `i` times shifted coefficient at the colour `n` is evaluating at `n + i`. -/
theorem evalAtField_iterate_coeffShift (n : ℤ) (i : ℕ) (c : Coeff) :
    evalAtField n (coeffShift^[i] c) = evalAtField (n + i) c := by
  induction i generalizing c with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih, evalAtField_coeffShift]
    congr 2
    push_cast
    ring

/-- The coefficient shift disappears at `t = -1`. -/
theorem map_evalRingHom_coeffShift (c : Coeff) :
    (coeffShift c).map (Polynomial.evalRingHom (-1 : ℤ)) =
      c.map (Polynomial.evalRingHom (-1 : ℤ)) := by
  have hcomp : coeffShift c = c.comp (C (X ^ 2) * X : Coeff) := rfl
  rw [hcomp, map_comp]
  simp

end AJConjecture
