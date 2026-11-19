import Mathlib
import AJFamily.Skein.TorusSequenceIdentity
import AJFamily.Quantum.FamTransferOpIrreducible
import AJFamily.Quantum.FamTransferRhsRational
import AJFamily.Quantum.FamTransferRhsNeZero
import AJFamily.Quantum.TorusNotEventuallyRational
import AJFamily.Quantum.FamSymbolFacts
import AJFamily.Quantum.TorusFormulaEven
import AJHandoff.LocalTheory.LocMinimalSpecialize
import AJHandoff.LocalTheory.LocTorusCycloPole

/-!
# The true minimal recurrence of the Whitehead doubles `W_k` of `T(2, 2k+1)`

For every `k ≥ 1`, with `a = 2k + 1`, `m = 2a` and the transfer operator `P_m` of order
`d = 2m + 3 = 8k + 7` (`famTransferOp`):

* the annihilators of positive tails of the reduced and of the unreduced sequence have minimal
  order exactly `8k + 8`;
* every recurrence polynomial of the coloured Jones function of `W_k` (the primitive generator of
  the rationally saturated all-integer annihilator) has order exactly `8k + 8`;
* its special symbol is `(L - 1)² E B_m` up to a unit of `ℚ(M)[L, L⁻¹]`.

For `k = 1` (the companion `T(2, 3)`, the seven-strand braid `W_1`): order `16` and special symbol
`(L - 1)² E B_6`. The library previously proved only the lower bound `8k + 8` (outside the
library) and `E ∣ f`.

Inputs: the transfer (`opApplyField_famTransferOp` through
`exists_coeff_mul_opApplyField_famTransferOp`,
`exists_forall_ge_opApplyField_famTransferOp_ne_zero`), irreducibility
(`natDegree_eq_zero_or_of_oreMul_eq_famTransferOp`), non-rationality
(`not_eventuallyRational_torusReducedFormulaEven`), the sequence identity
(`laurentToField_coloredJones_whiteheadTorusKnot`), the special symbol
(`specialize_famTransferOp_mul_eq`), and the tail extension through the closed formula's
cyclotomic expansion (`hasCyclotomicExpansion_torusWhiteheadFormula`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The order of the family's transfer operator: `d = 8k + 7`. -/
private theorem natDegree_famTransferOp_whitehead (k : ℕ) :
    (famTransferOp (2 * (2 * k + 1))).natDegree = 8 * k + 7 := by
  rw [natDegree_famTransferOp _ (by omega)]
  ring

/-- The family's transfer operator has no right pseudo-factor of intermediate order. -/
private theorem irreducible_famTransferOp_whitehead (k : ℕ) {β : Coeff} (hβ : β ≠ 0)
    {S R : RecOp} (h : C β * famTransferOp (2 * (2 * k + 1)) = oreMul coeffShift S R) :
    R.natDegree = 0 ∨ R.natDegree = (famTransferOp (2 * (2 * k + 1))).natDegree := by
  rw [natDegree_famTransferOp _ (by omega)]
  exact natDegree_eq_zero_or_of_oreMul_eq_famTransferOp _ (by omega) hβ h

/-- The sequence identity in `ℚ(t)` on positive colours. -/
private theorem laurentToField_coloredJones_whitehead_eq (k : ℕ) (hk : 1 ≤ k) (n : ℤ) :
    laurentToField (coloredJones (whiteheadTorusKnot k hk) n) =
      quantumInt n * torusReducedFormulaEven (2 * k + 1) n := by
  rw [laurentToField_coloredJones_whiteheadTorusKnot, torusWhiteheadFormula_eq_quantumInt_mul]

/-- Tail annihilators of the coloured Jones function annihilate it at every integer. -/
private theorem tailExtends_coloredJones_whitehead (k : ℕ) (hk : 1 ≤ k) :
    TailExtends fun n ↦ laurentToField (coloredJones (whiteheadTorusKnot k hk) n) := by
  have h : (fun n ↦ laurentToField (coloredJones (whiteheadTorusKnot k hk) n)) =
      torusWhiteheadFormula (2 * k + 1) :=
    funext fun n ↦ laurentToField_coloredJones_whiteheadTorusKnot k hk n
  rw [h]
  exact tailExtends_of_hasCyclotomicExpansion (hasCyclotomicExpansion_torusWhiteheadFormula _)

/-- The generic all-integer result, specialised to `W_k`. -/
private theorem natDegree_isRecurrencePolynomial_whitehead_aux (k : ℕ) (hk : 1 ≤ k) :
    (∃ α : RecOp, IsRecurrencePolynomial (coloredJones (whiteheadTorusKnot k hk)) α) ∧
      ∀ α : RecOp, IsRecurrencePolynomial (coloredJones (whiteheadTorusKnot k hk)) α →
        α.natDegree = (famTransferOp (2 * (2 * k + 1))).natDegree + 1 :=
  natDegree_isRecurrencePolynomial_of_transfer
    (by rw [natDegree_famTransferOp_whitehead]; omega)
    (irreducible_famTransferOp_whitehead k)
    (not_eventuallyRational_torusReducedFormulaEven _ (by omega))
    (exists_coeff_mul_opApplyField_famTransferOp _ (by omega))
    (exists_forall_ge_opApplyField_famTransferOp_ne_zero _ (by omega))
    (fun n _ ↦ laurentToField_coloredJones_whitehead_eq k hk n)
    (tailExtends_coloredJones_whitehead k hk)

/-- `X ^ n - 1` is a nonzero polynomial for `n ≥ 1`. -/
private theorem X_pow_sub_one_ne_zero_whitehead {n : ℕ} (hn : 0 < n) :
    (X ^ n - 1 : ℤ[X]) ≠ 0 := by
  simpa using X_pow_sub_C_ne_zero hn (1 : ℤ)

/-- `(L - 1) P(-1, M, L)` is `(L - 1)² E B_m` up to a unit, `m = 2(2k+1)`. -/
private theorem associated_specialize_famTransferOp_whitehead (k : ℕ) :
    Associated (toComparison ((X - 1) * specialize (famTransferOp (2 * (2 * k + 1)))))
      (toComparison ((X - 1) ^ 2 * extraFactor * twistPoly (2 * (2 * k + 1)))) := by
  set m := 2 * (2 * k + 1) with hm
  have h := specialize_famTransferOp_mul_eq m (by omega)
  set c₁ : ℤ[X] := (X ^ 2 - 1) ^ (2 * m + 3) * (X ^ 4 - 1) ^ (2 * m + 3) with hc₁
  set c₂ : ℤ[X] := (famDet m (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1)) with hc₂
  have h1 : c₁ ≠ 0 := mul_ne_zero (pow_ne_zero _ (X_pow_sub_one_ne_zero_whitehead two_pos))
    (pow_ne_zero _ (X_pow_sub_one_ne_zero_whitehead four_pos))
  have h2 : c₂ ≠ 0 := by
    rintro h0
    rw [h0, C_0, zero_mul] at h
    exact mul_ne_zero (C_ne_zero.mpr h1) (specialize_famTransferOp_ne_zero m (by omega)) h
  have h' : toComparison ((X - 1) * specialize (famTransferOp m)) * toComparison (C c₁) =
      toComparison (C c₂) * toComparison ((X - 1) ^ 2 * extraFactor * twistPoly m) := by
    rw [← map_mul, ← map_mul]
    congr 1
    linear_combination (X - 1 : ℤ[X][X]) * h
  refine (associated_mul_unit_left _ _ (isUnit_toComparison_coeff_of_ne_zero h1)).symm.trans ?_
  rw [h']
  exact associated_unit_mul_left _ _ (isUnit_toComparison_coeff_of_ne_zero h2)

/-- The tail minimal order of the family is `8k + 8`. -/
theorem tailOrder_whiteheadTorusKnot (k : ℕ) (hk : 1 ≤ k) :
    (∃ G : RecOp, G ≠ 0 ∧ G.natDegree = 8 * k + 8 ∧
        ∀ n : ℤ, 1 ≤ n → opApplyField G (torusWhiteheadFormula (2 * k + 1)) n = 0) ∧
      (∀ G : RecOp, G ≠ 0 →
        (∃ n₁ : ℤ, ∀ n : ℤ, n₁ ≤ n → opApplyField G (torusWhiteheadFormula (2 * k + 1)) n = 0) →
          8 * k + 8 ≤ G.natDegree) ∧
      (∃ G : RecOp, G ≠ 0 ∧ G.natDegree = 8 * k + 8 ∧
        ∀ n : ℤ, 1 ≤ n → opApplyField G (torusReducedFormulaEven (2 * k + 1)) n = 0) ∧
      ∀ G : RecOp, G ≠ 0 →
        (∃ n₁ : ℤ, ∀ n : ℤ, n₁ ≤ n →
          opApplyField G (torusReducedFormulaEven (2 * k + 1)) n = 0) →
          8 * k + 8 ≤ G.natDegree := by
  have h := tailOrder_of_transfer (by rw [natDegree_famTransferOp_whitehead]; omega)
    (irreducible_famTransferOp_whitehead k)
    (not_eventuallyRational_torusReducedFormulaEven _ (by omega))
    (exists_coeff_mul_opApplyField_famTransferOp _ (by omega))
    (exists_forall_ge_opApplyField_famTransferOp_ne_zero _ (by omega))
    (J := torusWhiteheadFormula (2 * k + 1))
    (fun n _ ↦ torusWhiteheadFormula_eq_quantumInt_mul _ n)
  rw [natDegree_famTransferOp_whitehead] at h
  exact ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩

/-- Every recurrence polynomial of `W_k` has order exactly `8k + 8`. -/
theorem natDegree_isRecurrencePolynomial_whiteheadTorusKnot (k : ℕ) (hk : 1 ≤ k) {α : RecOp}
    (hα : IsRecurrencePolynomial (coloredJones (whiteheadTorusKnot k hk)) α) :
    α.natDegree = 8 * k + 8 := by
  rw [(natDegree_isRecurrencePolynomial_whitehead_aux k hk).2 α hα,
    natDegree_famTransferOp_whitehead]

/-- The full primitive specialization: `α(-1, M, L) ≐ (L - 1)² E B_m`, `m = 2(2k+1)`. -/
theorem specialize_isRecurrencePolynomial_whiteheadTorusKnot (k : ℕ) (hk : 1 ≤ k) {α : RecOp}
    (hα : IsRecurrencePolynomial (coloredJones (whiteheadTorusKnot k hk)) α) :
    Associated (toComparison (specialize α))
      (toComparison ((X - 1) ^ 2 * extraFactor * twistPoly (2 * (2 * k + 1)))) := by
  refine (specialize_isRecurrencePolynomial_of_transfer
    (by rw [natDegree_famTransferOp_whitehead]; omega)
    (specialize_famTransferOp_ne_zero _ (by omega))
    (irreducible_famTransferOp_whitehead k)
    (not_eventuallyRational_torusReducedFormulaEven _ (by omega))
    (exists_coeff_mul_opApplyField_famTransferOp _ (by omega))
    (exists_forall_ge_opApplyField_famTransferOp_ne_zero _ (by omega))
    (fun n _ ↦ laurentToField_coloredJones_whitehead_eq k hk n)
    (tailExtends_coloredJones_whitehead k hk) hα).trans ?_
  exact associated_specialize_famTransferOp_whitehead k

/-- **The true minimal recurrence of `W_k`.** A recurrence polynomial exists, and every one has
order exactly `8k + 8` and special symbol `(L - 1)² E B_m`, `m = 2(2k+1)`, up to a unit. -/
theorem minimalRecurrence_whiteheadTorusKnot (k : ℕ) (hk : 1 ≤ k) :
    (∃ α : RecOp, IsRecurrencePolynomial (coloredJones (whiteheadTorusKnot k hk)) α) ∧
      ∀ α : RecOp, IsRecurrencePolynomial (coloredJones (whiteheadTorusKnot k hk)) α →
        α.natDegree = 8 * k + 8 ∧
          Associated (toComparison (specialize α))
            (toComparison ((X - 1) ^ 2 * extraFactor * twistPoly (2 * (2 * k + 1)))) := by
  refine ⟨?_, fun _ hα ↦ ⟨natDegree_isRecurrencePolynomial_whiteheadTorusKnot k hk hα,
    specialize_isRecurrencePolynomial_whiteheadTorusKnot k hk hα⟩⟩
  exact (natDegree_isRecurrencePolynomial_whitehead_aux k hk).1

/-- The case `k = 1` (`T(2, 3)`): a recurrence polynomial exists; every one has order `16` and
special symbol `(L - 1)² E B_6`. -/
theorem isRecurrencePolynomial_whiteheadTorusKnot_one :
    (∃ α : RecOp, IsRecurrencePolynomial (coloredJones (whiteheadTorusKnot 1 le_rfl)) α) ∧
      ∀ α : RecOp, IsRecurrencePolynomial (coloredJones (whiteheadTorusKnot 1 le_rfl)) α →
        α.natDegree = 16 ∧
          Associated (toComparison (specialize α))
            (toComparison ((X - 1) ^ 2 * extraFactor * twistPoly 6)) :=
  minimalRecurrence_whiteheadTorusKnot 1 le_rfl

end AJConjecture
