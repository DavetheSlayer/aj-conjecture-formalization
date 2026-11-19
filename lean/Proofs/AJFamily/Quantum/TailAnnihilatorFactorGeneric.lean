import Mathlib
import AJConjecture.QAlgHomogenizeOpApply
import AJFamily.Quantum.TailMinimalDegreeGeneric

/-!
# Tail annihilators factor through an irreducible operator

If the right pseudo-factors of `P` have degree `0` or `deg P`, `f` is not eventually rational, and
`P f` is eventually nonzero and rational in `M = t^(2n)`, then every annihilator of a tail of `f`
is a left multiple of `P` up to a nonzero scalar.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- If `δ · (P f) = β` on the colours `n ≥ 1` and `P f` is eventually nonzero, then the
numerator `β` is not zero. -/
private theorem ne_zero_of_coeff_mul_opApplyField_generic {P : RecOp} {f : ℤ → RatFunc ℚ}
    (hne : ∃ n₂ : ℤ, ∀ n : ℤ, n₂ ≤ n → opApplyField P f n ≠ 0) {β δ : Coeff}
    (hδ : δ ≠ 0) (hβδ : ∀ n : ℤ, 1 ≤ n →
      evalAtField n δ * opApplyField P f n = evalAtField n β) :
    β ≠ 0 := by
  rintro rfl
  obtain ⟨n₂, hn₂⟩ := hne
  obtain ⟨n₃, hn₃⟩ := exists_forall_ge_evalAtField_ne_zero hδ
  have h0 := hβδ (max 1 (max n₂ n₃)) (le_max_left _ _)
  rw [map_zero] at h0
  exact mul_ne_zero (hn₃ _ ((le_max_right _ _).trans (le_max_right _ _)))
    (hn₂ _ ((le_max_left _ _).trans (le_max_right _ _))) h0

/-- A left Ore multiple of an operator annihilating a tail annihilates the same tail. -/
private theorem opApplyField_oreMul_eq_zero_of_tail_generic {G : RecOp} {f : ℤ → RatFunc ℚ}
    {n₀ : ℤ} (hG : ∀ n : ℤ, n₀ ≤ n → opApplyField G f n = 0) (S : RecOp) {n : ℤ}
    (hn : n₀ ≤ n) : opApplyField (oreMul coeffShift S G) f n = 0 := by
  rw [opApplyField_oreMul, opApplyField_eq_sum_range]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hi : n₀ ≤ n + (i : ℤ) := hn.trans (le_add_of_nonneg_right (Int.natCast_nonneg i))
  rw [hG _ hi, mul_zero]

/-- Every annihilator of a tail of `f` is, up to a nonzero scalar, a left Ore multiple of `P`. -/
theorem exists_C_mul_eq_oreMul_of_tail_annihilator_of_irreducible {P : RecOp} {f : ℤ → RatFunc ℚ}
    (hP : P ≠ 0)
    (hirr : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      R.natDegree = 0 ∨ R.natDegree = P.natDegree)
    (hnr : ¬ EventuallyRational f)
    (hrhs : ∃ β δ : Coeff, δ ≠ 0 ∧ ∀ n : ℤ, 1 ≤ n →
      evalAtField n δ * opApplyField P f n = evalAtField n β)
    (hne : ∃ n₂ : ℤ, ∀ n : ℤ, n₂ ≤ n → opApplyField P f n ≠ 0)
    {Q' : RecOp} {n₁ : ℤ} (h : ∀ n : ℤ, n₁ ≤ n → opApplyField Q' f n = 0) :
    ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q' = oreMul coeffShift T P := by
  obtain ⟨β, δ, hδ, hβδ⟩ := hrhs
  have hβ : β ≠ 0 := ne_zero_of_coeff_mul_opApplyField_generic hne hδ hβδ
  have hGdeg : (homogenizeOp β δ P).natDegree = P.natDegree + 1 :=
    natDegree_homogenizeOp hβ hδ hP
  have hG0 : homogenizeOp β δ P ≠ 0 := fun h0 ↦ by
    rw [h0, natDegree_zero] at hGdeg
    omega
  have hGann : ∀ n : ℤ, 1 ≤ n → opApplyField (homogenizeOp β δ P) f n = 0 := fun n hn ↦
    opApplyField_homogenizeOp_eq_zero (hβδ n hn) (hβδ (n + 1) (by omega))
  obtain ⟨γ, hγ, S, Rem, hdiv, hdeg⟩ :=
    exists_C_mul_eq_oreMul_add coeffShift_injective Q' hG0
  have hRem : Rem = C γ * Q' - oreMul coeffShift S (homogenizeOp β δ P) := by
    rw [hdiv]
    ring
  have hRemAnn : ∀ n : ℤ, max n₁ 1 ≤ n → opApplyField Rem f n = 0 := by
    intro n hn
    rw [hRem, opApplyField_sub_left, opApplyField_C_mul_left,
      h n ((le_max_left _ _).trans hn), mul_zero,
      opApplyField_oreMul_eq_zero_of_tail_generic hGann S ((le_max_right _ _).trans hn),
      sub_zero]
  have hzero : Rem = 0 := by
    by_contra h0
    have hlt := natDegree_lt_natDegree h0 hdeg
    have hle := natDegree_lt_of_tail_annihilator_of_irreducible hP hirr hnr ⟨β, δ, hδ, hβδ⟩
      hne h0 hRemAnn
    omega
  refine ⟨γ, hγ, oreMul coeffShift S (C (β * coeffShift δ) * X - C (coeffShift β * δ)), ?_⟩
  rw [hdiv, hzero, add_zero, oreMul_assoc]
  rfl

end AJConjecture
