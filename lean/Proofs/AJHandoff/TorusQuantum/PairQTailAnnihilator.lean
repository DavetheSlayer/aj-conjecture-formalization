import Mathlib
import AJConjecture.QAlgHomogenizeOpApply
import AJFamily.Quantum.FamSymbolFacts
import AJFamily.Quantum.FamTransferOpIrreducible
import AJFamily.Quantum.TailAnnihilatorFactorGeneric
import AJHandoff.TorusQuantum.PairQTransferFacts
import AJHandoff.TorusQuantum.PairQNotRational

/-!
# Tail annihilators of the reduced sequence of `T(r, s)`

* `pairQ_exists_tail_annihilator`: a nonzero operator annihilates the even reduced sequence on
  the colours `n ≥ 1` (the homogenization of `P_(rs)` if the forcing is nonzero, else `δ P_(rs)`;
  as `exists_tail_annihilator_torusReducedFormulaEven`).
* `pairQ_exists_C_mul_eq_oreMul_famTransferOp`: every operator annihilating it on a tail is, up to
  a nonzero left coefficient, a left multiple of `P_(rs)` — the forcing-to-cyclicity theorem S of
  `sequence_interface.md`, from `exists_C_mul_eq_oreMul_of_tail_annihilator_of_irreducible`
  with T-IRR (`natDegree_eq_zero_or_of_oreMul_eq_famTransferOp`, `m = rs ≥ 2`), the
  nonrationality `pairQ_not_eventuallyRational_pair` and the two facts of `PairQTransferFacts`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

theorem pairQ_exists_tail_annihilator (r s : ℕ) (h : IsTorusPair r s) :
    ∃ G : RecOp, G ≠ 0 ∧ ∀ n : ℤ, 1 ≤ n →
      opApplyField G (pairQReducedFormulaEven (pairQOddColor r s)) n = 0 := by
  obtain ⟨β, δ, hδ, hβδ⟩ := pairQ_exists_coeff_mul_opApplyField_famTransferOp r s h
  have hm : 1 ≤ r * s := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := h.1; omega) (by have := h.2.1; omega))
  have hP : famTransferOp (r * s) ≠ 0 := fun h0 ↦ by
    have hdeg := natDegree_famTransferOp (r * s) hm
    rw [h0, natDegree_zero] at hdeg
    omega
  by_cases hβ : β = 0
  · refine ⟨C δ * famTransferOp (r * s), mul_ne_zero (C_ne_zero.mpr hδ) hP, fun n hn ↦ ?_⟩
    rw [opApplyField_C_mul_left, hβδ n hn, hβ, map_zero]
  · refine ⟨homogenizeOp β δ (famTransferOp (r * s)), fun h0 ↦ ?_, fun n hn ↦
      opApplyField_homogenizeOp_eq_zero (hβδ n hn) (hβδ (n + 1) (by omega))⟩
    have hdeg := natDegree_homogenizeOp hβ hδ hP
    rw [h0, natDegree_zero] at hdeg
    omega

theorem pairQ_exists_C_mul_eq_oreMul_famTransferOp (r s : ℕ) (h : IsTorusPair r s)
    {Q' : RecOp} {n₁ : ℤ}
    (hQ' : ∀ n : ℤ, n₁ ≤ n → opApplyField Q' (pairQReducedFormulaEven (pairQOddColor r s)) n = 0) :
    ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q' = oreMul coeffShift T (famTransferOp (r * s)) := by
  have hm : 1 ≤ r * s := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := h.1; omega) (by have := h.2.1; omega))
  have hP : famTransferOp (r * s) ≠ 0 := fun h0 ↦ by
    have hdeg := natDegree_famTransferOp (r * s) hm
    rw [h0, natDegree_zero] at hdeg
    omega
  refine exists_C_mul_eq_oreMul_of_tail_annihilator_of_irreducible hP ?_
    (pairQ_not_eventuallyRational_pair r s h.1 (by have := h.1; have := h.2.1; omega))
    (pairQ_exists_coeff_mul_opApplyField_famTransferOp r s h)
    (pairQ_exists_forall_ge_opApplyField_famTransferOp_ne_zero r s h) hQ'
  intro β hβ S R hR
  rw [natDegree_famTransferOp (r * s) hm]
  exact natDegree_eq_zero_or_of_oreMul_eq_famTransferOp (r * s)
    (by have h1 := h.1; have h2 := h.2.1; nlinarith) hβ hR

end AJConjecture
