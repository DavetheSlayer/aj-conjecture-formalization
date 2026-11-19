import Mathlib
import AJTwist.Exist.TwHGens
import AJTwist.Exist.TwHSpanStep

/-!
# The inner module is stable under the step operator

The step operator `V = cycloStep` maps every generator of `twHGen` into the saturated span of
the generators:

* `V S_0 D = 2 S_1 D` and `V S_i D = S_(i+1) D + q⁻¹ S_(i-1) D` for `i ≥ 1` (the recursion of
  the trace operators, `twH_cycloStep_cheb_zero`, `twH_cycloStep_cheb_succ`), and
  `S_i D` lies in the span for `i ≤ |a| + 1` (`twHSpan_gen_cheb`);
* `V 𝔊^(c) = 𝔊^(c+1) + q⁻¹ 𝔊^(c-1)` (`twH_cycloStep_gauss`), and every period lies in the span
  (`twHSpan_gen_gauss`).

Hence the span is stable under `V` (`twHSpan_cycloStep`) and contains `V^n D` for every `n`
(`twHSpan_gen_iterate`; `D = S_0 D / 2`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `V S_0 = 2 S_1`. -/
theorem twH_cycloStep_cheb_zero (y : ℕ → RatFunc ℚ) (j : ℕ) :
    cycloStep (cycloCheb 0 y) j = 2 * cycloCheb 1 y j := by
  rw [show cycloCheb 0 y = fun j ↦ 2 * y j from rfl, show cycloCheb 1 y = cycloStep y from rfl,
    cycloStep, cycloStep]
  ring

/-- `V S_(i+1) = S_(i+2) + q⁻¹ S_i`. -/
theorem twH_cycloStep_cheb_succ (i : ℕ) (y : ℕ → RatFunc ℚ) (j : ℕ) :
    cycloStep (cycloCheb (i + 1) y) j = cycloCheb (i + 2) y j + qParam⁻¹ * cycloCheb i y j := by
  rw [show cycloCheb (i + 2) y j =
    cycloStep (cycloCheb (i + 1) y) j - qParam⁻¹ * cycloCheb i y j from rfl]
  ring

/-- The step operator maps every generator into the span of the generators. -/
theorem twHSpan_gen_cycloStep (η : Bool) (r s : ℕ) (ℓ : ℤ)
    (k : Fin ((twIndex η r s ℓ).natAbs + 1) ⊕ Fin (2 * ℓ.natAbs + 1)) :
    TwHSpan (twHGen η r s ℓ) (cycloStep (twHGen η r s ℓ k)) := by
  rcases k with ⟨i, hi⟩ | k
  · rcases i with _ | i
    · have hfun : cycloStep (twHGen η r s ℓ (Sum.inl ⟨0, hi⟩)) = fun j ↦
          2 * cycloCheb 1 (pairQCycloCoeff (twInput η r s ℓ)) j :=
        funext fun j ↦ twH_cycloStep_cheb_zero _ j
      rw [hfun]
      exact twHSpan_constMul 2 (twHSpan_gen_cheb η r s ℓ (by omega))
    · have hfun : cycloStep (twHGen η r s ℓ (Sum.inl ⟨i + 1, hi⟩)) = fun j ↦
          cycloCheb (i + 2) (pairQCycloCoeff (twInput η r s ℓ)) j +
            qParam⁻¹ * cycloCheb i (pairQCycloCoeff (twInput η r s ℓ)) j :=
        funext fun j ↦ twH_cycloStep_cheb_succ i _ j
      rw [hfun]
      exact twHSpan_add (twHSpan_gen_cheb η r s ℓ (by omega))
        (twHSpan_constMul _ (twHSpan_gen_cheb η r s ℓ (by omega)))
  · have hfun : cycloStep (twHGen η r s ℓ (Sum.inr k)) = fun j ↦
        twHGauss ℓ ((k : ℕ) - (ℓ.natAbs : ℤ) + 1) j +
          qParam⁻¹ * twHGauss ℓ ((k : ℕ) - (ℓ.natAbs : ℤ) - 1) j :=
      funext fun j ↦ twH_cycloStep_gauss ℓ _ j
    rw [hfun]
    exact twHSpan_add (twHSpan_gen_gauss η r s ℓ _)
      (twHSpan_constMul _ (twHSpan_gen_gauss η r s ℓ _))

/-- All iterates `V^n D` of the cyclotomic coefficients of the twisted input lie in the span of
the generators. -/
theorem twHSpan_gen_iterate (η : Bool) (r s : ℕ) (ℓ : ℤ) (n : ℕ) :
    TwHSpan (twHGen η r s ℓ) (cycloStep^[n] (pairQCycloCoeff (twInput η r s ℓ))) := by
  refine twHSpan_iterate_cycloStep (twHSpan_gen_cycloStep η r s ℓ) ?_ n
  have h := twHSpan_constMul (2⁻¹ : RatFunc ℚ)
    (twHSpan_gen_cheb η r s ℓ (i := 0) (Nat.zero_le _))
  have hfun : (fun j ↦ (2⁻¹ : RatFunc ℚ) * cycloCheb 0 (pairQCycloCoeff (twInput η r s ℓ)) j) =
      pairQCycloCoeff (twInput η r s ℓ) := by
    funext j
    rw [cycloCheb, inv_mul_cancel_left₀ two_ne_zero]
  rwa [hfun] at h

end AJConjecture
