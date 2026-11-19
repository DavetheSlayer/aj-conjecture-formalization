import Mathlib
import AJConjecture.QAlgOpApplyFieldBasic
import AJFamily.Quantum.FamTransferMap
import AJFamily.Quantum.FamTransferOp
import AJFamily.Quantum.TorusFormulaEven
import AJFamily.Quantum.TorusInhomogeneousRecurrence

/-!
# The family transfer operator on the torus formula

`opApplyField_famTransferOp`: at colours `n ≥ 1`, `famTransferOp (2a)` applied to
`torusReducedFormulaEven a` is an explicit multiple of a sum of `a + 3` terms
`famKernel (2a) j N · torusCycloDefect a j`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The action is additive in the operator, for finite sums. -/
private theorem opApplyField_finsetSum_left_fam {ι : Type*} (s : Finset ι) (P : ι → RecOp)
    (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (∑ k ∈ s, P k) f n = ∑ k ∈ s, opApplyField (P k) f n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, opApplyField, sum_zero_index]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, opApplyField_add_left, ih]

/-- The value at the colour `n` of a coefficient of `famTransferOp m` is the Cramer coefficient
over `ℚ(t)` at `x = q^(n+(2m+3))`. -/
private theorem evalAtField_famCoeff_comp (m : ℕ) (n : ℤ) (i : Fin (2 * m + 4)) :
    evalAtField n ((famCoeff m (X ^ 4 : ℤ[X]) i).comp (C (X ^ (4 * (2 * m + 3))) * X ^ 2)) =
      (famCoeff m qParam i).eval (qParam ^ (n + (2 * m + 3 : ℕ))) := by
  have hφ : Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X (X ^ 4) = qParam := by
    rw [map_pow, coe_eval₂RingHom, eval₂_X, qParam]
  have hx : eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X)
      (RatFunc.X ^ (2 * n)) (C (X ^ (4 * (2 * m + 3))) * X ^ 2) =
        qParam ^ (n + (2 * m + 3 : ℕ)) := by
    rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, map_pow, coe_eval₂RingHom, eval₂_X, qParam,
      ← zpow_natCast RatFunc.X 4, ← zpow_natCast RatFunc.X (4 * (2 * m + 3)),
      ← zpow_natCast _ 2, ← zpow_mul, ← zpow_mul, ← zpow_add₀ RatFunc.X_ne_zero]
    congr 1
    push_cast
    ring
  rw [evalAtField, coe_eval₂RingHom, eval₂_comp, hx, eval₂_eq_eval_map, map_famCoeff, hφ]

/-- The action of the family transfer operator on the even extension of the reduced formula,
at the colours `n ≥ 1`. -/
theorem opApplyField_famTransferOp (a : ℕ) (ha : 1 ≤ a) {n : ℤ} (hn : 1 ≤ n) :
    opApplyField (famTransferOp (2 * a)) (torusReducedFormulaEven a) n =
      (famDet (2 * a) qParam).eval (qParam ^ (n + (4 * a + 3))) *
        (qParam ^ (4 * a + 3) * qParam ^ (n + (4 * a + 3))) ^ (2 * a + 1) *
          ∑ j ∈ Finset.range (a + 3), famKernel (2 * a) j (n + (4 * a + 3)) * torusCycloDefect a j := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
  have hm : 1 ≤ m := by exact_mod_cast hn
  have h := sum_famCoeff_mul_torusReducedFormula a ha (N := m + (4 * a + 3)) (by omega)
  have hcast : ((m + (4 * a + 3) : ℕ) : ℤ) = (m : ℤ) + (4 * a + 3) := by push_cast; ring
  rw [hcast] at h
  rw [← h, famTransferOp, opApplyField_finsetSum_left_fam]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun k ↦ ?_
  rw [C_mul_X_pow_eq_monomial, opApplyField_monomial, evalAtField_famCoeff_comp,
    Fin.revPerm_apply, torusReducedFormulaEven]
  have he : ((2 * (2 * a) + 3 : ℕ) : ℤ) = 4 * a + 3 := by push_cast; ring
  rw [he]
  congr 2
  rw [Fin.val_rev]
  omega

end AJConjecture
