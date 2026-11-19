import Mathlib

/-!
# Automorphisms of ℂ

An automorphism of a polynomial ring on a transcendence basis of `ℂ` extends to a ring
automorphism of `ℂ`. Consequently every irrational complex number, algebraic or transcendental,
is moved by some ring automorphism of `ℂ`, and a complex number fixed by all of them is rational.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- An automorphism of the polynomial ring on a transcendence basis of `ℂ` over `R` extends
to a ring automorphism of `ℂ`. -/
theorem exists_ringEquiv_extend {R : Type*} [Field R] [Algebra R ℂ] {ι : Type*} {v : ι → ℂ}
    (hv : IsTranscendenceBasis R v) (φ : MvPolynomial ι R ≃+* MvPolynomial ι R) :
    ∃ σ : ℂ ≃+* ℂ, ∀ p, σ (MvPolynomial.aeval v p) = MvPolynomial.aeval v (φ p) := by
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis v hv
  let e : Algebra.adjoin R (Set.range v) ≃+* Algebra.adjoin R (Set.range v) :=
    (hv.1.aevalEquiv.symm.toRingEquiv.trans φ).trans hv.1.aevalEquiv.toRingEquiv
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e, fun p ↦ ?_⟩
  have h1 : MvPolynomial.aeval v p =
      algebraMap (Algebra.adjoin R (Set.range v)) ℂ (hv.1.aevalEquiv p) := by
    simp [AlgebraicIndependent.aevalEquiv]
  have h2 : MvPolynomial.aeval v (φ p) =
      algebraMap (Algebra.adjoin R (Set.range v)) ℂ (hv.1.aevalEquiv (φ p)) := by
    simp [AlgebraicIndependent.aevalEquiv]
  rw [h1, h2, IsAlgClosure.equivOfEquiv_algebraMap]
  simp [e]

/-- A complex number transcendental over `ℚ` is moved by some ring automorphism of `ℂ`. -/
theorem exists_ringEquiv_ne_of_transcendental {z : ℂ} (hz : Transcendental ℚ z) :
    ∃ σ : ℂ ≃+* ℂ, σ z ≠ z := by
  have hind : AlgebraicIndepOn ℚ id ({z} : Set ℂ) :=
    (algebraicIndependent_singleton_iff (x := fun i : ({z} : Set ℂ) ↦ id (i : ℂ))
      ⟨z, rfl⟩).mpr hz
  obtain ⟨t, hzt, ht⟩ := exists_isTranscendenceBasis_superset hind
  let i₀ : t := ⟨z, hzt rfl⟩
  let f : MvPolynomial t ℚ →ₐ[ℚ] MvPolynomial t ℚ :=
    MvPolynomial.aeval fun i ↦ if i = i₀ then MvPolynomial.X i + 1 else MvPolynomial.X i
  let g : MvPolynomial t ℚ →ₐ[ℚ] MvPolynomial t ℚ :=
    MvPolynomial.aeval fun i ↦ if i = i₀ then MvPolynomial.X i - 1 else MvPolynomial.X i
  have hfg : f.comp g = AlgHom.id ℚ _ := by
    ext i; by_cases h : i = i₀ <;> simp [f, g, h]
  have hgf : g.comp f = AlgHom.id ℚ _ := by
    ext i; by_cases h : i = i₀ <;> simp [f, g, h]
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_extend ht (AlgEquiv.ofAlgHom f g hfg hgf).toRingEquiv
  refine ⟨σ, fun h ↦ ?_⟩
  have := hσ (MvPolynomial.X i₀)
  simp [f, i₀] at this
  rw [h] at this
  simp at this

/-- An algebraic irrational complex number is moved by some ring automorphism of `ℂ`. -/
theorem exists_ringEquiv_ne_of_isAlgebraic {z : ℂ} (hz : IsAlgebraic ℚ z)
    (hq : ∀ q : ℚ, (q : ℂ) ≠ z) : ∃ σ : ℂ ≃+* ℂ, σ z ≠ z := by
  let K := algebraicClosure ℚ ℂ
  have hzK : z ∈ K := mem_algebraicClosure_iff.mpr hz
  let zK : K := ⟨z, hzK⟩
  have hnot : zK ∉ (⊥ : IntermediateField ℚ K) := by
    intro h
    obtain ⟨q, hq'⟩ := IntermediateField.mem_bot.mp h
    exact hq q (by simpa [zK] using congrArg Subtype.val hq')
  obtain ⟨τ, hτ⟩ : ∃ τ : Gal(K/ℚ), τ zK ≠ zK := by
    by_contra hall
    push Not at hall
    exact hnot ((InfiniteGalois.mem_bot_iff_fixed zK).mpr hall)
  obtain ⟨ι, v, hv⟩ := exists_isTranscendenceBasis' K ℂ
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_extend hv (MvPolynomial.mapEquiv ι τ.toRingEquiv)
  refine ⟨σ, fun h ↦ hτ ?_⟩
  have := hσ (MvPolynomial.C zK)
  simp only [MvPolynomial.aeval_C, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C] at this
  apply Subtype.ext
  simpa [zK, h] using this.symm

/-- A complex number fixed by every ring automorphism of `ℂ` is rational. -/
theorem exists_rat_eq_of_forall_ringEquiv_fixed {z : ℂ} (h : ∀ σ : ℂ ≃+* ℂ, σ z = z) :
    ∃ q : ℚ, (q : ℂ) = z := by
  by_contra hq
  push Not at hq
  by_cases ha : IsAlgebraic ℚ z
  · obtain ⟨σ, hσ⟩ := exists_ringEquiv_ne_of_isAlgebraic ha hq
    exact hσ (h σ)
  · obtain ⟨σ, hσ⟩ := exists_ringEquiv_ne_of_transcendental (z := z) ha
    exact hσ (h σ)

end AJConjecture
