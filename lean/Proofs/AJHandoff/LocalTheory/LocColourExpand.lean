import Mathlib
import AJConjecture.WhiteheadFormula
import AJHandoff.LocalTheory.LocExpandAtOne

/-!
# The formal colour

Let `x` be a formal colour variable and substitute `t = e^u`, `M = t^(2x) = e^(2 x u)` in a
coefficient `a(t, M) ∈ ℤ[t][M]`: the result lies in `ℚ[x][[u]]`, each coefficient of `u^r` being
a polynomial in `x`. Evaluating `x` at an integer colour `n` gives the expansion at `t = 1` of the
value `a(t, t^(2n)) ∈ ℚ(t)` (`e^(2 n u) = (e^u)^(2n)`, `PowerSeries.exp_pow_eq_rescale_exp`, and
inverses for negative `n`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The formal colour expansion `ℤ[t][M] → ℚ[x][[u]]`, `t ↦ e^u`, `M ↦ e^(2 x u)`. -/
def colourExpand : Coeff →+* PowerSeries ℚ[X] :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (Int.castRingHom (PowerSeries ℚ[X])) (PowerSeries.exp ℚ[X]))
    (PowerSeries.rescale (2 * X : ℚ[X]) (PowerSeries.exp ℚ[X]))

/-- At an integer colour the formal colour gives the expansion of the value. -/
theorem colourExpand_eval (c : Coeff) (n : ℤ) :
    HahnSeries.ofPowerSeries ℤ ℚ ((colourExpand c).map (Polynomial.evalRingHom (n : ℚ))) =
      expandAtOne (evalAtField n c) := by
  let φ : Coeff →+* LaurentSeries ℚ := ((HahnSeries.ofPowerSeries ℤ ℚ).comp
    (PowerSeries.map (Polynomial.evalRingHom (n : ℚ)))).comp colourExpand
  let ψ : Coeff →+* LaurentSeries ℚ := expandAtOne.comp (evalAtField n)
  suffices h : φ = ψ from RingHom.congr_fun h c
  refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_) ?_
  · simp only [φ, ψ, RingHom.comp_apply, colourExpand, evalAtField, coe_eval₂RingHom, eval₂_C,
      eval₂_X, PowerSeries.map_exp]
    rw [← RatFunc.algebraMap_X, expandAtOne_algebraMap, aeval_X]
  · simp only [φ, ψ, RingHom.comp_apply, colourExpand, evalAtField, coe_eval₂RingHom, eval₂_X]
    rw [← PowerSeries.rescale_map, PowerSeries.map_exp, expandAtOne_X_zpow]
    congr 2
    simp

end AJConjecture
