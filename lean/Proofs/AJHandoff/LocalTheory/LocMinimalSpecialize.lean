import Mathlib
import AJConjecture.QAlgGaugeOpSpecialize
import AJConjecture.QAlgSpecializeDvdOfOreMul
import AJConjecture.QAlgPseudoFactorNormalize
import AJConjecture.RecurrencePolynomialUnique
import AJHandoff.LocalTheory.LocMinimalOrder

/-!
# The full primitive specialization of the true minimal recurrence

Under the hypotheses of `natDegree_isRecurrencePolynomial_of_transfer`, if moreover the special
symbol `P(-1, M, L)` is nonzero, then the special symbol of every recurrence polynomial `α` of `J`
is `(L - 1) P(-1, M, L)` up to a unit of `ℚ(M)[L, L⁻¹]` (a nonzero element of `ℚ(M)` times a power
of `L`).

Proof. Remove the powers of `t + 1` from the forcing (`β = (t+1)^a β'`, `δ = (t+1)^b δ'`); the
row `G = gauge((β' τ(δ') L - τ(β') δ') ⋆ P)` has order `d + 1`, annihilates `J` on positive
colours, and has special symbol `(M² - 1) β'(-1) δ'(-1) (L - 1) P(-1, M, L) ≠ 0`
(`specialize_gaugeOp`, `τ(c)(-1) = c(-1)`). `α` and `G` both have the minimal order `d + 1` in the
left ideal of tail annihilators of `J`, so each is a pseudo-left-multiple of the other by an
operator of order `0` (right pseudo-division and minimality), and
`toComparison_specialize_dvd_of_oreMul` gives divisibility of the special symbols both ways.
-/

open Polynomial
open scoped LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The value of a power of `t + 1` at any colour. -/
private theorem evalAtField_C_X_add_one_pow (n : ℤ) (k : ℕ) :
    evalAtField n (C ((X + 1 : ℤ[X]) ^ k)) = (RatFunc.X + 1 : RatFunc ℚ) ^ k := by
  simp only [evalAtField, coe_eval₂RingHom, eval₂_C, eval₂_pow, eval₂_add, eval₂_X, eval₂_one]

/-- `t + 1` is a nonzero rational function. -/
private theorem ratFuncX_add_one_ne_zero : (RatFunc.X + 1 : RatFunc ℚ) ≠ 0 := by
  have h : (RatFunc.X + 1 : RatFunc ℚ) = algebraMap ℚ[X] (RatFunc ℚ) (X + 1) := by
    rw [map_add, RatFunc.algebraMap_X, map_one]
  rw [h]
  exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr (X_add_C_ne_zero 1)

/-- The homogenised row of the normalised forcing annihilates `F` on positive colours. -/
private theorem opApplyField_homogenizeOp_normalized {P : RecOp} {F : ℤ → RatFunc ℚ}
    {a b : ℕ} {β' δ' : Coeff}
    (h : ∀ n : ℤ, 1 ≤ n → evalAtField n (C ((X + 1 : ℤ[X]) ^ b) * δ') * opApplyField P F n =
      evalAtField n (C ((X + 1 : ℤ[X]) ^ a) * β'))
    {n : ℤ} (hn : 1 ≤ n) : opApplyField (homogenizeOp β' δ' P) F n = 0 := by
  have h0 := h n hn
  have h1 := h (n + 1) (by omega)
  simp only [map_mul, evalAtField_C_X_add_one_pow] at h0 h1
  have he : (RatFunc.X + 1 : RatFunc ℚ) ^ b ≠ 0 := pow_ne_zero _ ratFuncX_add_one_ne_zero
  rw [opApplyField_homogenizeOp]
  refine (mul_eq_zero.mp ?_).resolve_left he
  linear_combination evalAtField n β' * h1 - evalAtField (n + 1) β' * h0

/-- The special symbol of the homogenised row of a normalised forcing. -/
private theorem specialize_homogenizeOp (β' δ' : Coeff) (P : RecOp) :
    specialize (homogenizeOp β' δ' P) =
      C (β'.map (Polynomial.evalRingHom (-1 : ℤ)) * δ'.map (Polynomial.evalRingHom (-1 : ℤ))) *
        ((X - 1) * specialize P) := by
  have hs : ∀ c : Coeff, (coeffShift c).map (Polynomial.evalRingHom (-1 : ℤ)) =
      c.map (Polynomial.evalRingHom (-1 : ℤ)) := fun c ↦ map_evalRingHom_iterate_coeffShift 1 c
  rw [homogenizeOp, specialize_oreMul, ← mul_assoc]
  congr 1
  simp only [specialize, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, Polynomial.map_mul, hs]
  ring

/-- A row of order at most `d + 1`, annihilating `J` on positive colours, whose special symbol is
`(L - 1) P(-1, M, L)` times a nonzero polynomial in `M`. -/
private theorem exists_row_specialize_of_transfer {F : ℤ → RatFunc ℚ} {P : RecOp}
    (hP : 0 < P.natDegree)
    (hrhs : ∃ β δ : Coeff, δ ≠ 0 ∧ ∀ n : ℤ, 1 ≤ n →
      evalAtField n δ * opApplyField P F n = evalAtField n β)
    (hne : ∃ n₂ : ℤ, ∀ n : ℤ, n₂ ≤ n → opApplyField P F n ≠ 0) {J : ℤ → RatFunc ℚ}
    (hJ : ∀ n : ℤ, 1 ≤ n → J n = quantumInt n * F n) :
    ∃ G : RecOp, G ≠ 0 ∧ G.natDegree ≤ P.natDegree + 1 ∧
      (∀ n : ℤ, 1 ≤ n → opApplyField G J n = 0) ∧
      ∃ u : ℤ[X], u ≠ 0 ∧ specialize G = C u * ((X - 1) * specialize P) := by
  have hP0 : P ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hP; exact lt_irrefl 0 hP
  obtain ⟨β, δ, hδ, hβδ⟩ := hrhs
  have hβ : β ≠ 0 := by
    rintro rfl
    obtain ⟨n₂, hn₂⟩ := hne
    obtain ⟨n₀, hn₀⟩ := exists_forall_ge_evalAtField_ne_zero hδ
    have h := hβδ (max (max n₂ n₀) 1) (le_max_right _ _)
    rw [map_zero] at h
    exact mul_ne_zero (hn₀ _ ((le_max_right _ _).trans (le_max_left _ _)))
      (hn₂ _ ((le_max_left _ _).trans (le_max_left _ _))) h
  obtain ⟨a, β', hβ'1, rfl⟩ := exists_pow_mul_map_ne_zero hβ
  obtain ⟨b, δ', hδ'1, rfl⟩ := exists_pow_mul_map_ne_zero hδ
  have hβ' : β' ≠ 0 := fun h ↦ hβ'1 (by rw [h, Polynomial.map_zero])
  have hδ' : δ' ≠ 0 := fun h ↦ hδ'1 (by rw [h, Polynomial.map_zero])
  have hHdeg := natDegree_homogenizeOp hβ' hδ' hP0
  have hH0 : homogenizeOp β' δ' P ≠ 0 := fun h ↦ by
    rw [h, natDegree_zero] at hHdeg
    omega
  obtain ⟨Q, hQ0, hQdeg, hQspec, hQ⟩ :=
    exists_gauge_quantumInt_mul_specialize (homogenizeOp β' δ' P)
  refine ⟨Q, hQ0 hH0, hHdeg ▸ hQdeg, fun n hn ↦ ?_,
    (X ^ 2 - 1) ^ (homogenizeOp β' δ' P).natDegree *
      (β'.map (Polynomial.evalRingHom (-1 : ℤ)) * δ'.map (Polynomial.evalRingHom (-1 : ℤ))),
    ?_, ?_⟩
  · have h := hQ F n (opApplyField_homogenizeOp_normalized hβδ hn)
    rw [opApplyField_eq_sum_range] at h ⊢
    rw [← h]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hJ (n + k) (by omega)]
  · exact mul_ne_zero (pow_ne_zero _ (fun h ↦ by
      have h2 := congrArg (fun p : ℤ[X] ↦ p.coeff 2) h
      simp only [coeff_sub, coeff_X_pow, coeff_one, coeff_zero] at h2
      norm_num at h2)) (mul_ne_zero hβ'1 hδ'1)
  · rw [hQspec, specialize_homogenizeOp, ← mul_assoc, ← C_mul]

/-- The special symbol of every recurrence polynomial is `(L - 1) P(-1, M, L)` up to a unit. -/
theorem specialize_isRecurrencePolynomial_of_transfer {J : ℤ → ℤ[T;T⁻¹]}
    {F : ℤ → RatFunc ℚ} {P : RecOp} (hP : 0 < P.natDegree) (hP0 : specialize P ≠ 0)
    (hirr : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      R.natDegree = 0 ∨ R.natDegree = P.natDegree)
    (hnr : ¬ EventuallyRational F)
    (hrhs : ∃ β δ : Coeff, δ ≠ 0 ∧ ∀ n : ℤ, 1 ≤ n →
      evalAtField n δ * opApplyField P F n = evalAtField n β)
    (hne : ∃ n₂ : ℤ, ∀ n : ℤ, n₂ ≤ n → opApplyField P F n ≠ 0)
    (hJF : ∀ n : ℤ, 1 ≤ n → laurentToField (J n) = quantumInt n * F n)
    (hext : TailExtends fun n ↦ laurentToField (J n)) {α : RecOp}
    (hα : IsRecurrencePolynomial J α) :
    Associated (toComparison (specialize α)) (toComparison ((X - 1) * specialize P)) := by
  obtain ⟨G, hG0, hGdeg, hG, u, hu, hGspec⟩ :=
    exists_row_specialize_of_transfer hP hrhs hne (J := fun n ↦ laurentToField (J n)) hJF
  have hGall := hext G ⟨1, hG⟩
  have hGin : InLocalizedAnnihilator J G := ⟨1, one_ne_zero, fun n ↦ by
    apply laurentToField_injective
    rw [map_one, one_mul, laurentToField_opApply, hGall n, map_zero]⟩
  have hαdeg := (natDegree_isRecurrencePolynomial_of_transfer hP hirr hnr hrhs hne hJF
    hext).2 α hα
  have hprim : IsRecurrencePolynomial J G.primPart := by
    refine ⟨G.primPart_ne_zero, ?_, fun Q hQ hQin ↦ ?_, G.isPrimitive_primPart⟩
    · obtain ⟨c, hc, hann⟩ := hGin
      refine ⟨c * G.content, mul_ne_zero hc (mt Polynomial.content_eq_zero_iff.mp hG0), ?_⟩
      rwa [Polynomial.C_mul, mul_assoc, ← Polynomial.eq_C_content_mul_primPart]
    · rw [Polynomial.natDegree_primPart]
      exact (hGdeg.trans hαdeg.ge).trans (hα.2.2.1 Q hQ hQin)
  have hassoc := isRecurrencePolynomial_associated hα hprim
  have hspec : toComparison (specialize (C G.content)) * toComparison (specialize G.primPart) =
      toComparison (C u) * toComparison ((X - 1) * specialize P) := by
    rw [← map_mul, ← map_mul, ← Polynomial.eq_C_content_mul_primPart, hGspec, map_mul]
  have hc : G.content.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 := by
    intro h0
    have hz : specialize G = 0 := by
      rw [Polynomial.eq_C_content_mul_primPart G, map_mul]
      simp only [specialize, coe_mapRingHom, Polynomial.map_C, h0, C_0, zero_mul]
    rw [hGspec] at hz
    refine mul_ne_zero (C_ne_zero.mpr hu) (mul_ne_zero (X_sub_C_ne_zero 1) hP0) hz
  have hcu : IsUnit (toComparison (specialize (C G.content))) := by
    simp only [specialize, coe_mapRingHom, Polynomial.map_C]
    exact isUnit_toComparison_coeff_of_ne_zero hc
  refine (hassoc.map (toComparison.comp specialize)).trans ?_
  simp only [RingHom.coe_comp, Function.comp_apply]
  refine (associated_unit_mul_left _ _ hcu).symm.trans ?_
  rw [hspec]
  exact associated_unit_mul_left _ _ (isUnit_toComparison_coeff_of_ne_zero hu)

end AJConjecture
