import Mathlib
import AJConjecture.QAlgQParamBasic

/-!
# A nonzero coefficient vanishes at finitely many colours

A nonzero `c ∈ ℤ[t][M]` is a nonzero polynomial in `M` over `ℚ(t)`, and the points `t^(2n)`,
`n ∈ ℤ`, are pairwise distinct because `t` is transcendental: `c(t, t^(2n)) = 0` for finitely
many `n` only.
-/

open Polynomial

namespace AJConjecture

/-- The evaluation `ℤ[t] → ℚ(t)` of the inner variable is the canonical embedding through
`ℚ[t]`. -/
private theorem eval₂RingHom_intCast_ratFuncX_eq_comp :
    Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X =
      (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
  refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
  · simp
  · simp [RatFunc.algebraMap_X]

/-- The evaluation `ℤ[t] → ℚ(t)` of the inner variable is injective. -/
private theorem eval₂RingHom_intCast_ratFuncX_injective :
    Function.Injective (Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X) := by
  rw [eval₂RingHom_intCast_ratFuncX_eq_comp, RingHom.coe_comp, coe_mapRingHom]
  exact (RatFunc.algebraMap_injective ℚ).comp (Polynomial.map_injective _ Int.cast_injective)

/-- A nonzero coefficient vanishes at finitely many colours. -/
theorem finite_setOf_evalAtField_eq_zero {c : Coeff} (hc : c ≠ 0) :
    {n : ℤ | evalAtField n c = 0}.Finite := by
  have hne : c.map (Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X) ≠ 0 :=
    (Polynomial.map_ne_zero_iff eval₂RingHom_intCast_ratFuncX_injective).mpr hc
  have hinj : Function.Injective fun n : ℤ ↦ (RatFunc.X : RatFunc ℚ) ^ (2 * n) := by
    intro m n h
    have h2 : 2 * m = 2 * n := ratFuncX_zpow_injective h
    omega
  refine ((Polynomial.finite_setOfPred_isRoot hne).preimage hinj.injOn).subset fun n hn ↦ ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, IsRoot.def, eval_map]
  exact hn

/-- A nonzero coefficient does not vanish at large colours. -/
theorem exists_forall_ge_evalAtField_ne_zero {c : Coeff} (hc : c ≠ 0) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → evalAtField n c ≠ 0 := by
  obtain ⟨B, hB⟩ := (finite_setOf_evalAtField_eq_zero hc).bddAbove
  refine ⟨B + 1, fun n hn h ↦ ?_⟩
  have hle : n ≤ B := hB h
  omega

end AJConjecture
