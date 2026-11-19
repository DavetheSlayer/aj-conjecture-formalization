import Mathlib
import AJFamily.Quantum.FamTransferOpIrreducible
import AJFamily.Quantum.FamTransferRhsNeZero
import AJFamily.Quantum.FamTransferRhsRational
import AJFamily.Quantum.TailAnnihilatorFactorGeneric
import AJFamily.Quantum.TorusNotEventuallyRational

/-!
# Tail annihilators factor through the family operator

For `a ≥ 2`, every tail annihilator of the even reduced formula is a left multiple of
`famTransferOp (2a)` up to a nonzero scalar.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

theorem exists_C_mul_eq_oreMul_famTransferOp_of_tail_annihilator (a : ℕ) (ha : 2 ≤ a) {Q' : RecOp}
    {n₁ : ℤ} (h : ∀ n : ℤ, n₁ ≤ n → opApplyField Q' (torusReducedFormulaEven a) n = 0) :
    ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q' = oreMul coeffShift T (famTransferOp (2 * a)) := by
  have hm : 1 ≤ 2 * a := by omega
  have hP : famTransferOp (2 * a) ≠ 0 := fun h0 ↦ by
    have := natDegree_famTransferOp (2 * a) hm
    rw [h0, natDegree_zero] at this
    omega
  refine exists_C_mul_eq_oreMul_of_tail_annihilator_of_irreducible hP ?_
    (not_eventuallyRational_torusReducedFormulaEven a ha)
    (exists_coeff_mul_opApplyField_famTransferOp a (by omega))
    (exists_forall_ge_opApplyField_famTransferOp_ne_zero a (by omega)) h
  intro β hβ S R hR
  rw [natDegree_famTransferOp (2 * a) hm]
  exact natDegree_eq_zero_or_of_oreMul_eq_famTransferOp (2 * a) (by omega) hβ hR

end AJConjecture
