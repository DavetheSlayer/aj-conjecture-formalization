import Mathlib
import AJConjecture.QAlgDualJet
import AJFamily.Quantum.FamJetData
import AJFamily.Quantum.FamTransferMap
import AJFamily.Quantum.FamTransferOp

/-!
# The family transfer operator at `t = -1 + ε`

`evalDualPoint_famTransferOp`: at `t = -1 + ε`, `M = m₀`, the coefficients of `famTransferOp m`
are the Cramer coefficients at `q = 1 - 4ε`, `x = famDualX m m₀`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The dual evaluation of a power of `t` is a power of `-1 + ε`. -/
private theorem dualJetHom_X_pow_famDual (n : ℕ) :
    dualJetHom (X ^ n) = (-1 + DualNumber.eps) ^ n := by
  rw [map_pow, dualJetHom, coe_eval₂RingHom, eval₂_X]

/-- `(-1 + ε)^n = (-1)^n + n (-1)^(n-1) ε`. -/
private theorem neg_one_add_eps_pow_famDual (n : ℕ) :
    (-1 + DualNumber.eps : DualNumber ℂ) ^ n =
      TrivSqZeroExt.inl ((-1) ^ n) +
        TrivSqZeroExt.inl ((n : ℂ) * (-1) ^ (n - 1)) * DualNumber.eps := by
  ext
  · simp
  · simp [TrivSqZeroExt.snd_pow]

/-- `(-1 + ε)^(4n) = 1 - 4n ε` for `n ≥ 1`. -/
private theorem neg_one_add_eps_pow_four_mul_famDual (n : ℕ) (hn : 1 ≤ n) :
    (-1 + DualNumber.eps : DualNumber ℂ) ^ (4 * n) =
      1 - ((4 * n : ℕ) : DualNumber ℂ) * DualNumber.eps := by
  rw [neg_one_add_eps_pow_famDual]
  have he : Even (4 * n) := ⟨2 * n, by ring⟩
  have ho : Odd (4 * n - 1) := ⟨2 * n - 1, by omega⟩
  rw [he.neg_one_pow, ho.neg_one_pow, ← TrivSqZeroExt.inl_natCast, sub_eq_add_neg]
  ext <;> simp

/-- The value of `q = t⁴` at `t = -1 + ε` is `1 - 4ε`. -/
private theorem dualJetHom_X_pow_four_famDual : dualJetHom (X ^ 4) = dualQ := by
  have h := neg_one_add_eps_pow_four_mul_famDual 1 le_rfl
  rw [mul_one] at h
  rw [dualJetHom_X_pow_famDual, h, dualQ]
  norm_num

/-- The value of `x = t^(4d) M²` at `t = -1 + ε`, `M = m₀` is `(1 - 4dε) m₀²`. -/
private theorem dualJetHom_X_pow_mul_famDual (m : ℕ) (m₀ : ℂ) :
    dualJetHom (X ^ (4 * (2 * m + 3))) * TrivSqZeroExt.inl m₀ ^ 2 = famDualX m m₀ := by
  rw [dualJetHom_X_pow_famDual, neg_one_add_eps_pow_four_mul_famDual _ (by omega), famDualX,
    ← TrivSqZeroExt.inl_pow]

theorem evalDualPoint_famTransferOp (m : ℕ) (m₀ l : ℂ) :
    evalDualPoint (famTransferOp m) m₀ l =
      ∑ k : Fin (2 * m + 4), (famCoeff m dualQ (Fin.rev k)).eval (famDualX m m₀) *
        TrivSqZeroExt.inl l ^ (k : ℕ) := by
  rw [evalDualPoint, famTransferOp, Polynomial.map_sum, ← coe_evalEvalRingHom, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coe_evalEvalRingHom, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, coe_mapRingHom,
    Polynomial.map_comp, map_famCoeff, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C,
    evalEval_mul, evalEval_pow, evalEval_X, evalEval_C, eval_comp, eval_mul, eval_pow, eval_X,
    eval_C, dualJetHom_X_pow_four_famDual, dualJetHom_X_pow_mul_famDual]

end AJConjecture
