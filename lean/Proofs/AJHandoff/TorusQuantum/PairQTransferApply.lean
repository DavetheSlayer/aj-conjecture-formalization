import Mathlib
import AJConjecture.QAlgOpApplyFieldBasic
import AJFamily.Quantum.FamTransferMap
import AJFamily.Quantum.FamTransferOp
import AJHandoff.TorusQuantum.PairQInhomRec

/-!
# T-TRANSFER: the transfer operator applied to the reduced sequence of `T(r, s)`

`pairQ_opApplyField_famTransferOp`: for every admissible pair and every colour `n ≥ 1`,
`(P_(rs) F)(n) = pairQTransferRhs (rs) (r+s+1) e n`, where `P_m = famTransferOp m` is the
transfer operator of order `d = 2m + 3` (it depends only on `m = rs`), `F` is the even reduced
sequence of `u = pairQOddColor r s` and `e` its defect: the identity `P_m F = ρ` of source Q10 on
the colours `N = n + d > d`, with forcing determined by the defects `e_j`, `j < c = r + s + 1`.
Route (as `opApplyField_famTransferOp`): unfold the action, `ev_n(t^(4d) M²) = q^(n+d)`, transport
the Cramer coefficients by `map_famCoeff`, and apply `pairQ_sum_famCoeff_mul_reducedFormula`
with `N = n + d`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The action is additive in the operator, for finite sums. -/
private theorem opApplyField_finsetSum_left_pairQ {ι : Type*} (s : Finset ι) (P : ι → RecOp)
    (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (∑ k ∈ s, P k) f n = ∑ k ∈ s, opApplyField (P k) f n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, opApplyField, sum_zero_index]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, opApplyField_add_left, ih]

/-- The value at the colour `n` of a coefficient of `famTransferOp m` is the Cramer coefficient
over `ℚ(t)` at `x = q^(n+(2m+3))`. -/
private theorem evalAtField_famCoeff_comp_pairQ (m : ℕ) (n : ℤ) (i : Fin (2 * m + 4)) :
    evalAtField n ((famCoeff m (X ^ 4 : ℤ[X]) i).comp (C (X ^ (4 * (2 * m + 3))) * X ^ 2)) =
      (famCoeff m qParam i).eval (qParam ^ (n + (2 * m + 3 : ℕ))) := by
  have hφ : Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X (X ^ 4) =
      qParam := by
    rw [map_pow, coe_eval₂RingHom, eval₂_X, qParam]
  have hx : eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X)
      (RatFunc.X ^ (2 * n)) (C (X ^ (4 * (2 * m + 3))) * X ^ 2) =
        qParam ^ (n + (2 * m + 3 : ℕ)) := by
    rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, map_pow, coe_eval₂RingHom, eval₂_X,
      qParam,
      ← zpow_natCast RatFunc.X 4, ← zpow_natCast RatFunc.X (4 * (2 * m + 3)),
      ← zpow_natCast _ 2, ← zpow_mul, ← zpow_mul, ← zpow_add₀ RatFunc.X_ne_zero]
    congr 1
    push_cast
    ring
  rw [evalAtField, coe_eval₂RingHom, eval₂_comp, hx, eval₂_eq_eval_map, map_famCoeff, hφ]

theorem pairQ_opApplyField_famTransferOp (r s : ℕ) (h : IsTorusPair r s) {n : ℤ}
    (hn : 1 ≤ n) :
    opApplyField (famTransferOp (r * s)) (pairQReducedFormulaEven (pairQOddColor r s)) n =
      pairQTransferRhs (r * s) (r + s + 1) (pairQCycloDefect (r * s) (pairQOddColor r s)) n := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
  have hk : 1 ≤ k := by exact_mod_cast hn
  have h := pairQ_sum_famCoeff_mul_reducedFormula r s h (N := k + (2 * (r * s) + 3))
    (by omega)
  generalize r * s = m at h ⊢
  have hcast : ((k + (2 * m + 3) : ℕ) : ℤ) = (k : ℤ) + (2 * m + 3) := by push_cast; ring
  rw [hcast] at h
  rw [pairQTransferRhs, ← h, famTransferOp, opApplyField_finsetSum_left_pairQ]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i ↦ ?_
  rw [C_mul_X_pow_eq_monomial, opApplyField_monomial, evalAtField_famCoeff_comp_pairQ,
    Fin.revPerm_apply, pairQReducedFormulaEven]
  have he : ((2 * m + 3 : ℕ) : ℤ) = 2 * m + 3 := by push_cast; ring
  rw [he]
  congr 2
  rw [Fin.val_rev]
  omega

end AJConjecture
