import Mathlib
import AJConjecture.QAlgEvalAtFieldZeros
import AJConjecture.QAlgEventuallyRationalClosure
import AJConjecture.QAlgOrePseudoDivision

/-!
# Minimal degree of tail annihilators

The operators mapping `f` to eventually rational sequences are closed under pseudo-division; with
the irreducibility of `P`, every nonzero annihilator of a tail of `f` has degree larger than `P`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- A nonzero operator of minimal degree among those mapping `f` to an eventually rational
sequence is a right pseudo-factor of every operator with that property. -/
private theorem exists_C_mul_eq_oreMul_of_minimalDegree_generic {f : ℤ → RatFunc ℚ}
    {Q : RecOp} (hQ0 : Q ≠ 0) (hQ : EventuallyRational fun n ↦ opApplyField Q f n)
    (hmin : ∀ Q' : RecOp, Q' ≠ 0 → (EventuallyRational fun n ↦ opApplyField Q' f n) →
      Q.natDegree ≤ Q'.natDegree)
    {P : RecOp} (hP : EventuallyRational fun n ↦ opApplyField P f n) :
    ∃ γ : Coeff, γ ≠ 0 ∧ ∃ S : RecOp, C γ * P = oreMul coeffShift S Q := by
  obtain ⟨γ, hγ, S, Rem, hdiv, hdeg⟩ := exists_C_mul_eq_oreMul_add coeffShift_injective P hQ0
  have hRem : Rem = C γ * P - oreMul coeffShift S Q := by
    rw [hdiv]
    ring
  have hmem : EventuallyRational fun n ↦ opApplyField Rem f n := by
    rw [hRem]
    exact eventuallyRational_opApplyField_sub (eventuallyRational_opApplyField_C_mul hP γ)
      (eventuallyRational_opApplyField_oreMul hQ S)
  have hzero : Rem = 0 := by
    by_contra h0
    have hlt := natDegree_lt_natDegree h0 hdeg
    have hle := hmin Rem h0 hmem
    omega
  refine ⟨γ, hγ, S, ?_⟩
  rw [hdiv, hzero, add_zero]

/-- If `f` is not eventually rational, no nonzero operator of degree `0` maps it to an
eventually rational sequence. -/
private theorem natDegree_ne_zero_of_eventuallyRational_generic {f : ℤ → RatFunc ℚ}
    (hnr : ¬ EventuallyRational f) {Q : RecOp} (hQ0 : Q ≠ 0)
    (hQ : EventuallyRational fun n ↦ opApplyField Q f n) :
    Q.natDegree ≠ 0 := by
  intro hdeg
  obtain ⟨c, rfl⟩ : ∃ c, Q = C c := ⟨Q.coeff 0, eq_C_of_natDegree_eq_zero hdeg⟩
  have hc : c ≠ 0 := fun h0 ↦ hQ0 (by rw [h0, C_0])
  obtain ⟨a, b, hb, n₀, hab⟩ := hQ
  refine hnr ⟨a, b * c, mul_ne_zero hb hc, n₀, fun n hn ↦ ?_⟩
  have happly : opApplyField (C c) f n = evalAtField n c * f n := by
    rw [← monomial_zero_left, opApplyField_monomial, Nat.cast_zero, add_zero]
  rw [map_mul, mul_assoc, ← happly]
  exact hab n hn

/-- An operator annihilating the tail of `f` is not a right pseudo-factor of an operator `P`
whose image of `f` is eventually nonzero. -/
private theorem not_oreMul_eq_of_tail_annihilator_generic {f : ℤ → RatFunc ℚ} {P : RecOp}
    (hne : ∃ n₂ : ℤ, ∀ n : ℤ, n₂ ≤ n → opApplyField P f n ≠ 0) {γ : Coeff}
    (hγ : γ ≠ 0) {S R : RecOp} (hfac : C γ * P = oreMul coeffShift S R) {n₁ : ℤ}
    (h : ∀ n : ℤ, n₁ ≤ n → opApplyField R f n = 0) : False := by
  obtain ⟨n₂, hn₂⟩ := hne
  obtain ⟨n₃, hn₃⟩ := exists_forall_ge_evalAtField_ne_zero hγ
  have hne' : opApplyField (C γ * P) f (max n₁ (max n₂ n₃)) ≠ 0 := by
    rw [opApplyField_C_mul_left]
    exact mul_ne_zero (hn₃ _ ((le_max_right _ _).trans (le_max_right _ _)))
      (hn₂ _ ((le_max_left _ _).trans (le_max_right _ _)))
  apply hne'
  rw [hfac, opApplyField_oreMul, opApplyField_eq_sum_range]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hi : n₁ ≤ max n₁ (max n₂ n₃) + (i : ℤ) :=
    (le_max_left _ _).trans (le_add_of_nonneg_right (Int.natCast_nonneg i))
  rw [h _ hi, mul_zero]

set_option linter.unusedVariables false in
/-- Every nonzero annihilator of a tail of `f` has degree larger than `P`. -/
theorem natDegree_lt_of_tail_annihilator_of_irreducible {P : RecOp} {f : ℤ → RatFunc ℚ}
    (hP : P ≠ 0)
    (hirr : ∀ {β : Coeff}, β ≠ 0 → ∀ {S R : RecOp}, C β * P = oreMul coeffShift S R →
      R.natDegree = 0 ∨ R.natDegree = P.natDegree)
    (hnr : ¬ EventuallyRational f)
    (hrhs : ∃ β δ : Coeff, δ ≠ 0 ∧ ∀ n : ℤ, 1 ≤ n →
      evalAtField n δ * opApplyField P f n = evalAtField n β)
    (hne : ∃ n₂ : ℤ, ∀ n : ℤ, n₂ ≤ n → opApplyField P f n ≠ 0)
    {R : RecOp} (hR : R ≠ 0) {n₁ : ℤ} (h : ∀ n : ℤ, n₁ ≤ n → opApplyField R f n = 0) :
    P.natDegree < R.natDegree := by
  classical
  by_contra hlt
  have hPmem : EventuallyRational fun n ↦ opApplyField P f n := by
    obtain ⟨β, δ, hδ, hβδ⟩ := hrhs
    exact ⟨β, δ, hδ, 1, hβδ⟩
  have hRmem : EventuallyRational fun n ↦ opApplyField R f n :=
    eventuallyRational_of_forall_ge_eq_zero h
  have hex : ∃ d : ℕ, ∃ Q : RecOp, Q ≠ 0 ∧
      (EventuallyRational fun n ↦ opApplyField Q f n) ∧ Q.natDegree = d :=
    ⟨_, R, hR, hRmem, rfl⟩
  obtain ⟨Q, hQ0, hQmem, hQd⟩ := Nat.find_spec hex
  have hmin : ∀ Q' : RecOp, Q' ≠ 0 →
      (EventuallyRational fun n ↦ opApplyField Q' f n) →
      Q.natDegree ≤ Q'.natDegree := fun Q' h0 hm ↦ by
    rw [hQd]
    exact Nat.find_min' hex ⟨Q', h0, hm, rfl⟩
  obtain ⟨γ, hγ, S, hfac⟩ :=
    exists_C_mul_eq_oreMul_of_minimalDegree_generic hQ0 hQmem hmin hPmem
  rcases hirr hγ hfac with h0 | hdeg
  · exact natDegree_ne_zero_of_eventuallyRational_generic hnr hQ0 hQmem h0
  · have hRmin : ∀ Q' : RecOp, Q' ≠ 0 →
        (EventuallyRational fun n ↦ opApplyField Q' f n) →
        R.natDegree ≤ Q'.natDegree := fun Q' h0 hm ↦ by
      have h1 := hmin Q' h0 hm
      have h2 := hmin R hR hRmem
      omega
    obtain ⟨γ', hγ', S', hfac'⟩ :=
      exists_C_mul_eq_oreMul_of_minimalDegree_generic hR hRmem hRmin hPmem
    exact not_oreMul_eq_of_tail_annihilator_generic hne hγ' hfac' h

end AJConjecture
