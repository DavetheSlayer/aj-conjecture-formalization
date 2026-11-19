import Mathlib
import AJConjecture.QAlgOreMulMap
import AJConjecture.QAlgOreMulDegree
import AJConjecture.QAlgOreMulAssoc
import AJConjecture.QAlgOreMulZero

/-!
# Factorizations over a fraction field and pseudo-factorizations

Let `A` be a domain with an injective endomorphism `σ`, `K` its fraction field and `τ` an
endomorphism of `K` extending `σ`. A factorization of `P ∈ A[u]` in `K[u; τ]` is, after clearing
denominators on the right factor and then on the left, a pseudo-factorization `β P = S ⋆ R` in
`A[u; σ]` with the same degrees; conversely `β P = S ⋆ R` gives `P = (β⁻¹ S) ⋆ R` over `K`. So
irreducibility of `P` in `K[u; τ]` is the absence of right pseudo-factors of intermediate degree,
and `G = H ⋆ P` over `K` means `β G = H' ⋆ P` over `A`. This is the library's Remark on
`ℚ(t, M)[L; τ]` (not formalized there), stated for every such `A ⊆ K`; it serves both
`ℂ[[h]][z] ⊆ ℂ((h))(z)` and `ℤ[t][M] ⊆ ℚ(t, M)`.

For `P` with nonzero constant coefficient, irreducibility in the polynomial ring `K[u; τ]` and in
the Laurent ring `K[u, u⁻¹; τ]` (up to the units `a u^k`) agree.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `P` is irreducible in `K[u; τ]`: of positive degree, and every factorization `P = S ⋆ R` has a
factor of degree `0`. -/
def OreIrreducible {K : Type*} [Field K] (τ : K →+* K) (P : K[X]) : Prop :=
  0 < P.natDegree ∧ ∀ S R : K[X], oreMul τ S R = P → R.natDegree = 0 ∨ S.natDegree = 0

/-- Left multiplication by a constant commutes with the Ore product on the left factor. -/
private theorem oreMul_C_mul_left_pseudoField {A : Type*} [CommRing A] (σ : A →+* A) (c : A)
    (P Q : A[X]) : oreMul σ (C c * P) Q = C c * oreMul σ P Q := by
  rw [← oreMul_C_left, oreMul_assoc, oreMul_C_left]

/-- Clearing the denominators of a polynomial over the fraction field. -/
private theorem exists_map_eq_C_mul_pseudoField {A K : Type*} [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] (p : K[X]) :
    ∃ b : A, b ≠ 0 ∧ ∃ q : A[X], q.map (algebraMap A K) = C (algebraMap A K b) * p := by
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) p
  refine ⟨b, nonZeroDivisors.ne_zero hb,
    IsLocalization.integerNormalization (nonZeroDivisors A) p, ?_⟩
  rw [hq, Algebra.smul_def, Polynomial.algebraMap_apply]

theorem oreIrreducible_map_iff {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (σ : A →+* A) (τ : K →+* K)
    (hτ : ∀ a : A, τ (algebraMap A K a) = algebraMap A K (σ a)) {P : A[X]}
    (hP : 0 < P.natDegree) :
    OreIrreducible τ (P.map (algebraMap A K)) ↔
      ∀ {β : A}, β ≠ 0 → ∀ {S R : A[X]}, C β * P = oreMul σ S R →
        R.natDegree = 0 ∨ R.natDegree = P.natDegree := by
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hmap : ∀ S R : A[X], (oreMul σ S R).map (algebraMap A K) =
      oreMul τ (S.map (algebraMap A K)) (R.map (algebraMap A K)) :=
    map_oreMul _ σ τ fun a ↦ (hτ a).symm
  have hdeg : ∀ Q : A[X], (Q.map (algebraMap A K)).natDegree = Q.natDegree :=
    fun Q ↦ Polynomial.natDegree_map_eq_of_injective hinj Q
  have hP0 : P.map (algebraMap A K) ≠ 0 := by
    intro h0
    have := hdeg P
    rw [h0, Polynomial.natDegree_zero] at this
    omega
  constructor
  · rintro ⟨-, hirr⟩ β hβ S R h
    have hβK : algebraMap A K β ≠ 0 := (map_ne_zero_iff _ hinj).mpr hβ
    have hK : oreMul τ (C (algebraMap A K β)⁻¹ * S.map (algebraMap A K)) (R.map (algebraMap A K))
        = P.map (algebraMap A K) := by
      rw [oreMul_C_mul_left_pseudoField, ← hmap, ← h, Polynomial.map_mul, Polynomial.map_C,
        ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hβK, Polynomial.C_1, one_mul]
    rcases hirr _ _ hK with hR | hS
    · exact Or.inl (by rw [← hdeg R, hR])
    · right
      have hS0 : C (algebraMap A K β)⁻¹ * S.map (algebraMap A K) ≠ 0 := by
        rintro h0; rw [h0, oreMul_zero_left] at hK; exact hP0 hK.symm
      have hR0 : R.map (algebraMap A K) ≠ 0 := by
        rintro h0; rw [h0, oreMul_zero_right] at hK; exact hP0 hK.symm
      have := natDegree_oreMul τ.injective hS0 hR0
      rw [hK, hdeg, hdeg, hS, zero_add] at this
      exact this.symm
  · intro hpseudo
    refine ⟨by rwa [hdeg], fun S R h ↦ ?_⟩
    obtain ⟨b, hb, R', hR'⟩ := exists_map_eq_C_mul_pseudoField (A := A) R
    have hbK : algebraMap A K b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb
    obtain ⟨a, ha, S', hS'⟩ :=
      exists_map_eq_C_mul_pseudoField (A := A) (oreMul τ S (C (algebraMap A K b)⁻¹))
    have hRK : R = C (algebraMap A K b)⁻¹ * R'.map (algebraMap A K) := by
      rw [hR', ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hbK, Polynomial.C_1, one_mul]
    have hfac : C a * P = oreMul σ S' R' := by
      refine Polynomial.map_injective _ hinj ?_
      rw [hmap, hS', oreMul_C_mul_left_pseudoField, oreMul_assoc, oreMul_C_left, ← hRK, h,
        Polynomial.map_mul, Polynomial.map_C]
    have hRdeg : R.natDegree = R'.natDegree := by
      rw [← hdeg R', hR', Polynomial.natDegree_C_mul hbK]
    rcases hpseudo ha hfac with h0 | h1
    · exact Or.inl (hRdeg.trans h0)
    · right
      have hS0 : S ≠ 0 := by
        rintro h0; rw [h0, oreMul_zero_left] at h; exact hP0 h.symm
      have hR0 : R ≠ 0 := by
        rintro h0; rw [h0, oreMul_zero_right] at h; exact hP0 h.symm
      have := natDegree_oreMul τ.injective hS0 hR0
      rw [h, hdeg, hRdeg, h1] at this
      omega

theorem exists_C_mul_eq_oreMul_of_map_eq {A K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (σ : A →+* A) (τ : K →+* K)
    (hτ : ∀ a : A, τ (algebraMap A K a) = algebraMap A K (σ a)) {G P : A[X]} {H : K[X]}
    (h : G.map (algebraMap A K) = oreMul τ H (P.map (algebraMap A K))) :
    ∃ β : A, β ≠ 0 ∧ ∃ H' : A[X], C β * G = oreMul σ H' P := by
  obtain ⟨b, hb, q, hq⟩ := exists_map_eq_C_mul_pseudoField (A := A) H
  refine ⟨b, hb, q, Polynomial.map_injective _ (IsFractionRing.injective A K) ?_⟩
  rw [map_oreMul _ σ τ (fun a ↦ (hτ a).symm), hq, oreMul_C_mul_left_pseudoField, ← h,
    Polynomial.map_mul, Polynomial.map_C]

end AJConjecture
