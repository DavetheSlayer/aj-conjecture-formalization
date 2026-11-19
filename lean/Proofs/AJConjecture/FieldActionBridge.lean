import Mathlib
import AJConjecture.WhiteheadFormula

/-!
# Recurrence operators commute with the embedding into `ℚ(t)`

The embedding `ℤ[t, t⁻¹] → ℚ(t)` is injective and intertwines the action of recurrence
operators on sequences of Laurent polynomials with their action on sequences in `ℚ(t)`.
-/

open Polynomial LaurentPolynomial

namespace AJConjecture

/-- On ordinary polynomials, the embedding `ℤ[t, t⁻¹] → ℚ(t)` is the cast to `ℚ[t]`. -/
private theorem laurentToField_toLaurent (p : ℤ[X]) :
    laurentToField (toLaurent p) =
      algebraMap ℚ[X] (RatFunc ℚ) (p.map (Int.castRingHom ℚ)) := by
  rw [laurentToField, LaurentPolynomial.eval₂_toLaurent, Units.val_mk0, Polynomial.map,
    Polynomial.hom_eval₂, RatFunc.algebraMap_X]
  congr 1
  exact RingHom.ext_int _ _

/-- The embedding `ℤ[t, t⁻¹] → ℚ(t)` sends `t ^ n` to `t ^ n`. -/
theorem laurentToField_T (n : ℤ) :
    laurentToField (T n) = (RatFunc.X : RatFunc ℚ) ^ n := by
  rw [laurentToField, LaurentPolynomial.eval₂_T, Units.val_zpow_eq_zpow_val, Units.val_mk0]

/-- The embedding `ℤ[t, t⁻¹] → ℚ(t)` is injective. -/
theorem laurentToField_injective : Function.Injective laurentToField := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨n, p', hp'⟩ := LaurentPolynomial.exists_T_pow p
  have hzero : algebraMap ℚ[X] (RatFunc ℚ) (p'.map (Int.castRingHom ℚ)) = 0 := by
    rw [← laurentToField_toLaurent, hp', map_mul, hp, zero_mul]
  have hmap : p'.map (Int.castRingHom ℚ) = 0 :=
    (map_eq_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mp hzero
  have hp0 : p' = 0 :=
    Polynomial.map_injective _ Int.cast_injective (hmap.trans (Polynomial.map_zero _).symm)
  rw [hp0, map_zero] at hp'
  exact ((LaurentPolynomial.isUnit_T (n : ℤ)).mul_left_eq_zero.mp hp'.symm)

/-- The embedding `ℤ[t, t⁻¹] → ℚ(t)` intertwines the two evaluations of coefficients. -/
private theorem laurentToField_comp_evalAt (n : ℤ) :
    laurentToField.comp (evalAt n) = evalAtField n := by
  refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
  · have hinner : (laurentToField.comp (evalAt n)).comp Polynomial.C =
        (evalAtField n).comp Polynomial.C := by
      refine Polynomial.ringHom_ext (fun b ↦ ?_) ?_
      · simp [evalAt, evalAtField]
      · simp [evalAt, evalAtField, laurentToField_T]
    exact DFunLike.congr_fun hinner a
  · simp [evalAt, evalAtField, laurentToField_T]

/-- The embedding `ℤ[t, t⁻¹] → ℚ(t)` intertwines the two actions of recurrence operators. -/
theorem laurentToField_opApply (P : RecOp) (g : ℤ → ℤ[T;T⁻¹]) (n : ℤ) :
    laurentToField (opApply P g n) = opApplyField P (fun m ↦ laurentToField (g m)) n := by
  simp only [opApply, opApplyField, Polynomial.sum_def, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← laurentToField_comp_evalAt, RingHom.comp_apply]

end AJConjecture
