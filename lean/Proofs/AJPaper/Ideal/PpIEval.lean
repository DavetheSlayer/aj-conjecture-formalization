import Mathlib
import AJPaper.Ideal.PpIDefs

/-!
# Evaluation of the torus algebra at a point (Unit PpI, node `PpI_Eval`)

The value `ppiEval p g = ∑ g_{k,l} M^k L^l` of `g ∈ 𝔱 = ℂ[M^{±1}, L^{±1}]` at `p = (M, L)`.
For `M, L ≠ 0` it is a ring homomorphism in `g` (`ppiEval_add`, `ppiEval_mul`, `ppiEval_one`);
the involution `σ` of `𝔱` corresponds to the simultaneous inversion of the point
(`ppiEval_ppiSigma`).

Route: `ppiEval p` is `AddMonoidAlgebra.lift` of the monoid homomorphism
`(k, l) ↦ M^k L^l` when `M, L ≠ 0` (`zpow_add₀`); additivity is `Finsupp.sum_add_index'`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

theorem ppiEval_single (p : ℂ × ℂ) (kl : ℤ × ℤ) (c : ℂ) :
    ppiEval p (AddMonoidAlgebra.single kl c) = c * p.1 ^ kl.1 * p.2 ^ kl.2 := by
  rw [ppiEval, AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index]
  rw [zero_mul, zero_mul]

theorem ppiEval_add (p : ℂ × ℂ) (g h : PpiTorus) :
    ppiEval p (g + h) = ppiEval p g + ppiEval p h := by
  rw [ppiEval, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index']
  · rfl
  · intro kl
    rw [zero_mul, zero_mul]
  · intro kl c d
    rw [add_mul, add_mul]

theorem ppiEval_one (p : ℂ × ℂ) : ppiEval p 1 = 1 := by
  rw [AddMonoidAlgebra.one_def, ppiEval_single]
  simp

/-- The value of `0` is `0`. -/
private theorem ppiEval_zero_ppiEval (p : ℂ × ℂ) : ppiEval p 0 = 0 := by
  rw [ppiEval, AddMonoidAlgebra.coeff_zero, Finsupp.sum_zero_index]

/-- At a point with nonzero coordinates the evaluation is multiplicative. -/
theorem ppiEval_mul {p : ℂ × ℂ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0) (g h : PpiTorus) :
    ppiEval p (g * h) = ppiEval p g * ppiEval p h := by
  induction g using AddMonoidAlgebra.induction_linear with
  | zero => rw [zero_mul, ppiEval_zero_ppiEval, zero_mul]
  | add x y hx hy => rw [add_mul, ppiEval_add, ppiEval_add, hx, hy, add_mul]
  | single m c =>
    induction h using AddMonoidAlgebra.induction_linear with
    | zero => rw [mul_zero, ppiEval_zero_ppiEval, mul_zero]
    | add x y hx hy => rw [mul_add, ppiEval_add, ppiEval_add, hx, hy, mul_add]
    | single n d =>
      rw [AddMonoidAlgebra.single_mul_single, ppiEval_single, ppiEval_single, ppiEval_single,
        Prod.fst_add, Prod.snd_add, zpow_add₀ h1, zpow_add₀ h2]
      ring

/-- The value of `σ g` at `(M, L)` is the value of `g` at `(M⁻¹, L⁻¹)`. -/
theorem ppiEval_ppiSigma (p : ℂ × ℂ) (g : PpiTorus) :
    ppiEval p (ppiSigma g) = ppiEval (p.1⁻¹, p.2⁻¹) g := by
  induction g using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, ppiEval_zero_ppiEval, ppiEval_zero_ppiEval]
  | add x y hx hy => rw [map_add, ppiEval_add, ppiEval_add, hx, hy]
  | single m c =>
    rw [ppiSigma, AddMonoidAlgebra.domCongr_single, ppiEval_single, ppiEval_single,
      AddEquiv.neg_apply, Prod.fst_neg, Prod.snd_neg, zpow_neg, zpow_neg, inv_zpow, inv_zpow]

end AJConjecture
