import Mathlib
import AJConjecture.QAlgQParamBasic
import AJFamily.Quantum.FamTransferPoly

/-!
# The family summation kernel

`famKernel m j N`, the cyclotomic kernel divided by the common denominator `famBasisPoly m q 0`,
which does not vanish at `(q^N, q^j)` for `N ≥ 2m + 4`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The summation kernel `G_j(N) = C_j(N) / Δ(q^N, q^j)`. -/
def famKernel (m : ℕ) (j : ℕ) (N : ℤ) : RatFunc ℚ :=
  cyclotomicKernel j N / (famBasisPoly m qParam 0).evalEval (qParam ^ N) (qParam ^ j)

/-- The common denominator `Δ(q^N, q^j)` does not vanish for `N ≥ 2m + 4`. -/
theorem famBasisPoly_zero_evalEval_ne_zero (m : ℕ) {N : ℤ} (hN : 2 * (m : ℤ) + 4 ≤ N) (j : ℕ) :
    (famBasisPoly m qParam 0).evalEval (qParam ^ N) (qParam ^ j) ≠ 0 := by
  have hpow : ∀ a b : ℤ, a ≠ b → qParam ^ a - qParam ^ b ≠ 0 := fun a b hab h ↦
    hab (qParam_zpow_injective (sub_eq_zero.mp h))
  simp only [famBasisPoly, Finset.range_zero, Finset.prod_empty, one_mul, evalEval_prod,
    evalEval_mul, evalEval_sub, evalEval_C, evalEval_X, eval_sub, eval_C, eval_X]
  rw [Finset.prod_ne_zero_iff]
  intro r hr
  have hr' : r < 2 * m + 3 := (Finset.mem_Ico.mp hr).2
  refine mul_ne_zero ?_ ?_
  · have h := hpow N ((r + 1 : ℕ) : ℤ) (by omega)
    rwa [zpow_natCast] at h
  · have h := hpow (r : ℤ) (N + j) (by omega)
    rwa [zpow_natCast, zpow_add₀ qParam_ne_zero, zpow_natCast] at h

end AJConjecture
