import Mathlib
import AJHandoff.TorusQuantum.PairQTransferApply
import AJHandoff.TorusQuantum.PairQTransferRhs
import AJHandoff.TorusQuantum.PairQTransferRhsNeZero
import AJHandoff.TorusQuantum.PairQCycloDefectZero

/-!
# The forcing of `T(r, s)` is rational and eventually nonzero

For every admissible pair, `n ↦ (P_(rs) F)(n)` is, on the colours `n ≥ 1`, the evaluation of a
quotient of two elements of `ℤ[t][M]`, and it is nonzero for all large `n`. From
`pairQ_opApplyField_famTransferOp`, `pairQ_exists_coeff_mul_transferRhs`,
`pairQ_transferRhs_eventually_ne_zero`, and `e_0 = 2(1 - q) ≠ 0` (`pairQCycloDefect_zero`,
`pairQOddColor_zero`). These are the analogues of `exists_coeff_mul_opApplyField_famTransferOp`
and `exists_forall_ge_opApplyField_famTransferOp_ne_zero`.
-/

noncomputable section

namespace AJConjecture

theorem pairQ_exists_coeff_mul_opApplyField_famTransferOp (r s : ℕ) (h : IsTorusPair r s) :
    ∃ β δ : Coeff, δ ≠ 0 ∧ ∀ n : ℤ, 1 ≤ n →
      evalAtField n δ *
          opApplyField (famTransferOp (r * s)) (pairQReducedFormulaEven (pairQOddColor r s)) n =
        evalAtField n β := by
  have hm : 1 ≤ r * s :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by have := h.1; omega) (by have := h.2.1; omega))
  obtain ⟨β, δ, hδ, hβ⟩ := pairQ_exists_coeff_mul_transferRhs (r * s) hm (r + s + 1)
    (pairQCycloDefect (r * s) (pairQOddColor r s))
  refine ⟨β, δ, hδ, fun n hn ↦ ?_⟩
  rw [pairQ_opApplyField_famTransferOp r s h hn]
  exact hβ n hn

theorem pairQ_exists_forall_ge_opApplyField_famTransferOp_ne_zero (r s : ℕ)
    (h : IsTorusPair r s) :
    ∃ n₁ : ℤ, ∀ n : ℤ, n₁ ≤ n →
      opApplyField (famTransferOp (r * s)) (pairQReducedFormulaEven (pairQOddColor r s)) n ≠ 0 := by
  have hm : 1 ≤ r * s :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by have := h.1; omega) (by have := h.2.1; omega))
  have he : pairQCycloDefect (r * s) (pairQOddColor r s) 0 ≠ 0 := by
    rw [pairQCycloDefect_zero (r * s) hm _ (pairQOddColor_zero r s)]
    have h1 := one_sub_qParam_zpow_ne_zero (n := 1) one_ne_zero
    rw [zpow_one] at h1
    exact mul_ne_zero two_ne_zero h1
  obtain ⟨n₁, hn₁⟩ := pairQ_transferRhs_eventually_ne_zero (r * s) hm
    (c := r + s + 1) (by omega) he
  refine ⟨max 1 n₁, fun n hn ↦ ?_⟩
  rw [pairQ_opApplyField_famTransferOp r s h ((le_max_left 1 n₁).trans hn)]
  exact hn₁ n ((le_max_right 1 n₁).trans hn)

end AJConjecture
