import Mathlib
import AJFamily.Quantum.NodeCriterionCollision
import AJFamily.Quantum.AbNodeNoSeparation
import AJFamily.Quantum.FamSymbolFacts
import AJConjecture.ExtraFactorPrime
import AJTwist.Factor.TwFOneEbNode
import AJTwist.Factor.TwFOnePrime
import AJTwist.Factor.TwFOneEbCollision
import AJTwist.Factor.TwFOneWeyl

/-!
# No right factor of `P_1` separates `E` from `B_1` (TwF, unit F3)

Source: revision 5, Section 5.5 (`operators.tex`): "The simple crossing with `E` has already
forced `E` and `B_1` into the same factor of any partition."

`toComparison_extraFactor_dvd_iff_twistPoly_one_dvd`: the symbol of a right pseudo-factor of
`famTransferOp 1` is divisible by `E` exactly when it is divisible by `B_1`.

Route: `toComparison_extraFactor_dvd_iff_twistPoly_dvd`
(`AJFamily/Quantum/EbNodeNoSeparation.lean`, stated for `m ≥ 2`) with `m = 1`: the index criterion
`toComparison_dvd_specialize_of_weylSymbol_eq_zero_collision` in both directions with
`G, D ∈ {E, B_1}`, `T = L - 1`, the symbol `specialize_famTransferOp_mul_eq 1`, the end
coefficients `eval_coeff_specialize_famTransferOp_ne_zero 1`, the scalars
`eval_symbolLeft_ne_zero 1`, `eval_symbolRight_ne_zero 1`, the degrees
`natDegree_specialize_famTransferOp 1`, `natDegree_famTransferOp 1` (all stated for `m ≥ 1`),
and `famOne_ebNode_facts`, `famOne_ebNode_collisionFree`,
`evalIntPoint_weylSymbol_famTransferOp_one_ebNode`, `prime_toComparison_twistPoly_one`,
`prime_toComparison_extraFactor`. A node point exists since `ℂ` is algebraically closed.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- There is a point `m₀` of the `E/B_1` node equation. -/
private theorem exists_ebNode_root_twfOneEbNoSep :
    ∃ m₀ : ℂ, 3 * (m₀ ^ 2) ^ 2 + 7 * m₀ ^ 2 + 3 = 0 := by
  obtain ⟨x, hx⟩ := exists_quadratic_eq_zero (three_ne_zero (α := ℂ))
    (IsAlgClosed.isSquare (discrim (3 : ℂ) 7 3))
  obtain ⟨m₀, hm₀⟩ := IsAlgClosed.exists_pow_nat_eq x two_pos
  exact ⟨m₀, by rw [hm₀]; linear_combination hx⟩

/-- No right pseudo-factor of `P_1` separates `E` from `B_1`. -/
theorem toComparison_extraFactor_dvd_iff_twistPoly_one_dvd {β : Coeff} (hβ : β ≠ 0)
    {S R : RecOp} (h : C β * famTransferOp 1 = oreMul coeffShift S R) :
    toComparison extraFactor ∣ toComparison (specialize R) ↔
      toComparison (twistPoly 1) ∣ toComparison (specialize R) := by
  obtain ⟨m₀, heb⟩ := exists_ebNode_root_twfOneEbNoSep
  obtain ⟨h0, h1, h2, -, -, hl0, hT, hE, hB, hEL, hBL, hJac⟩ := famOne_ebNode_facts heb
  obtain ⟨hlead, hconst⟩ :=
    eval_coeff_specialize_famTransferOp_ne_zero 1 le_rfl h0 h1 h2
  have hdeg : (specialize (famTransferOp 1)).natDegree = (famTransferOp 1).natDegree := by
    rw [natDegree_specialize_famTransferOp 1 le_rfl, natDegree_famTransferOp 1 le_rfl]
  have hcoll := famOne_ebNode_collisionFree heb
  have hW := evalIntPoint_weylSymbol_famTransferOp_one_ebNode heb
  constructor
  · refine toComparison_dvd_specialize_of_weylSymbol_eq_zero_collision (G := extraFactor)
      (D := twistPoly 1) (T := X - 1) ?_ prime_toComparison_twistPoly_one h0 hl0
      (eval_symbolLeft_ne_zero 1 h1 h2) (eval_symbolRight_ne_zero 1 h1 h2)
      hdeg hlead hconst hE hB hT hEL hBL hJac hcoll hW hβ h
    rw [specialize_famTransferOp_mul_eq 1 le_rfl]
    ring
  · refine toComparison_dvd_specialize_of_weylSymbol_eq_zero_collision (G := twistPoly 1)
      (D := extraFactor) (T := X - 1) ?_ prime_toComparison_extraFactor h0 hl0
      (eval_symbolLeft_ne_zero 1 h1 h2) (eval_symbolRight_ne_zero 1 h1 h2)
      hdeg hlead hconst hB hE hT hBL hEL ?_ hcoll.symm hW hβ h
    · rw [specialize_famTransferOp_mul_eq 1 le_rfl]
      ring
    · intro hJ
      exact hJac (by linear_combination -hJ)

end AJConjecture
