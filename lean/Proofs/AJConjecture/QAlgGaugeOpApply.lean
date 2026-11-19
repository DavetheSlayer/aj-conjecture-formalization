import Mathlib
import AJFamily.Quantum.TorusOddColorRec
import AJConjecture.QAlgGaugeOp
import AJConjecture.QAlgOpApplyFieldBasic
import AJConjecture.QAlgQParamBasic

/-!
# The action of the gauged operator

`(gaugeOp Q) g (n) = t^(2 deg Q + 2n) (t² - t⁻²) · (Q ([·] g))(n)` at every integer colour `n`.
-/

open Polynomial

namespace AJConjecture

/-- The action of recurrence operators is additive over finite sums of operators. -/
private theorem opApplyField_finsetSum_left_gaugeOp {ι : Type*} (s : Finset ι) (P : ι → RecOp)
    (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (∑ i ∈ s, P i) f n = ∑ i ∈ s, opApplyField (P i) f n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [opApplyField]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, opApplyField_add_left, ih]

/-- The value of the gauge factor of `L^k` at the colour `n` is
`t^(2r + 2n) (t² - t⁻²) [n + k]`. -/
private theorem evalAtField_gaugeOp_factor {r k : ℕ} (hk : k ≤ r) (n : ℤ) :
    evalAtField n (C (X ^ (2 * (r - k))) * (C (X ^ (4 * k)) * X ^ 2 - 1)) =
      RatFunc.X ^ (2 * (r : ℤ) + 2 * n) * (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) *
        quantumInt (n + k) := by
  have hT : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hL : evalAtField n (C (X ^ (2 * (r - k))) * (C (X ^ (4 * k)) * X ^ 2 - 1)) =
      RatFunc.X ^ (2 * (r - k)) * (RatFunc.X ^ (4 * k) * (RatFunc.X ^ (2 * n)) ^ 2 - 1) := by
    simp only [evalAtField, coe_eval₂RingHom, eval₂_mul, eval₂_sub, eval₂_C, eval₂_X, eval₂_pow,
      eval₂_one]
  have e1 : (RatFunc.X : RatFunc ℚ) ^ (2 * (r - k)) = RatFunc.X ^ (2 * (r : ℤ) - 2 * k) := by
    rw [← zpow_natCast]
    congr 1
    omega
  have e2 : (RatFunc.X : RatFunc ℚ) ^ (4 * k) = RatFunc.X ^ (4 * (k : ℤ)) := by
    rw [← zpow_natCast]
    congr 1
  have e3 : ((RatFunc.X : RatFunc ℚ) ^ (2 * n)) ^ 2 = RatFunc.X ^ (4 * n) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [hL, e1, e2, e3, quantumInt, mul_assoc,
    mul_div_cancel₀ _ ratFuncX_sq_sub_inv_sq_ne_zero, mul_sub, mul_sub, mul_one,
    ← zpow_add₀ hT, ← zpow_add₀ hT, ← zpow_add₀ hT, ← zpow_add₀ hT]
  congr 2 <;> ring

/-- The gauged operator acts on `g` as `Q` acts on `n ↦ [n] g(n)`, up to a nonzero factor. -/
theorem opApplyField_gaugeOp (Q : RecOp) (g : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (gaugeOp Q) g n =
      RatFunc.X ^ (2 * (Q.natDegree : ℤ) + 2 * n) * (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) *
        opApplyField Q (fun m ↦ quantumInt m * g m) n := by
  have hR : opApplyField Q (fun m ↦ quantumInt m * g m) n =
      ∑ k ∈ Q.support, evalAtField n (Q.coeff k) * (quantumInt (n + k) * g (n + k)) := rfl
  rw [gaugeOp, Polynomial.sum_def, opApplyField_finsetSum_left_gaugeOp, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [opApplyField_monomial, map_mul,
    evalAtField_gaugeOp_factor (Polynomial.le_natDegree_of_mem_supp k hk)]
  ring

end AJConjecture
