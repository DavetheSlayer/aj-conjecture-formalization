import Mathlib
import AJConjecture.APolynomial
import AJFamily.Classical.ComplexAutomorphisms
import AJFamily.Classical.FamilyPolynomials

/-!
# Galois descent for bivariate polynomials

Field automorphisms `σ` of `ℂ` act on `ℂ[M][L]` coefficientwise and on `ℂ²` coordinatewise,
compatibly with evaluation and normalisation. The Zariski closure of an automorphism-stable set
and the eigenvalue set of a knot are automorphism-stable, and a polynomial fixed by every `σ` is
a nonzero scalar multiple of one with integer coefficients.
-/

open Polynomial

noncomputable section

namespace AJConjecture

theorem evalPoint_map_ringEquiv (σ : ℂ ≃+* ℂ) (P : ℂ[X][X]) (p : ℂ × ℂ) :
    evalPoint (P.map (Polynomial.mapRingHom (σ : ℂ →+* ℂ))) (σ p.1, σ p.2) =
      σ (evalPoint P p) := by
  have hcomp : (Polynomial.evalRingHom (σ p.1)).comp (Polynomial.mapRingHom (σ : ℂ →+* ℂ)) =
      (σ : ℂ →+* ℂ).comp (Polynomial.evalRingHom p.1) := by
    ext q <;> simp
  simp only [evalPoint, Polynomial.eval₂_map, hcomp]
  exact (Polynomial.hom_eval₂ P _ (σ : ℂ →+* ℂ) p.2).symm

/-- A subset of `ℂ²` stable under all field automorphisms of `ℂ` acting on both coordinates. -/
def IsAutStable (S : Set (ℂ × ℂ)) : Prop :=
  ∀ σ : ℂ ≃+* ℂ, ∀ p ∈ S, (σ p.1, σ p.2) ∈ S

theorem zariskiClosure_isAutStable {S : Set (ℂ × ℂ)} (hS : IsAutStable S) :
    IsAutStable (zariskiClosure S) := by
  intro σ p hp P hP
  set Q : ℂ[X][X] := P.map (Polynomial.mapRingHom (σ.symm : ℂ →+* ℂ)) with hQ
  have hQP : Q.map (Polynomial.mapRingHom (σ : ℂ →+* ℂ)) = P := by
    rw [hQ, Polynomial.map_map, Polynomial.mapRingHom_comp]
    simp
  have hQS : ∀ s ∈ S, evalPoint Q s = 0 := by
    intro s hs
    have h1 := evalPoint_map_ringEquiv σ Q s
    rw [hQP, hP _ (hS σ s hs)] at h1
    exact (map_eq_zero_iff σ σ.injective).1 h1.symm
  have h2 := evalPoint_map_ringEquiv σ Q p
  rw [hQP] at h2
  rw [h2, hp Q hQS, map_zero]

theorem eigenvalueSet_isAutStable (K : BraidKnot) : IsAutStable (eigenvalueSet K) := by
  rintro σ p ⟨ρ, h1, h2, h3, h4⟩
  refine ⟨(Matrix.SpecialLinearGroup.map (σ : ℂ →+* ℂ)).comp ρ, ?_, ?_, ?_, ?_⟩
  · change σ _ = 0
    rw [h1, map_zero]
  · change σ _ = 0
    rw [h2, map_zero]
  · change σ _ = _
    rw [h3]
  · change σ _ = _
    rw [h4]

theorem exists_int_poly_of_forall_ringEquiv_fixed (A₀ : ℂ[X][X])
    (h : ∀ σ : ℂ ≃+* ℂ, A₀.map (Polynomial.mapRingHom (σ : ℂ →+* ℂ)) = A₀) :
    ∃ (A : ℤ[X][X]) (c : ℂ), c ≠ 0 ∧ mapC A = C (C c) * A₀ := by
  have hfix : ∀ i j : ℕ, ∃ q : ℚ, (q : ℂ) = (A₀.coeff i).coeff j := by
    intro i j
    apply exists_rat_eq_of_forall_ringEquiv_fixed
    intro σ
    have := congrArg (fun P : ℂ[X][X] ↦ (P.coeff i).coeff j) (h σ)
    simpa [Polynomial.coeff_map] using this
  choose q hq using hfix
  set N : ℕ := ∏ i ∈ A₀.support, ∏ j ∈ (A₀.coeff i).support, (q i j).den with hN
  have hN0 : (N : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun i _ ↦ Finset.prod_ne_zero_iff.2 fun j _ ↦ (q i j).den_nz
  have hlift : C (C (N : ℂ)) * A₀ ∈
      Polynomial.lifts (Polynomial.mapRingHom (Int.castRingHom ℂ)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_C_mul]
    have hi : C (N : ℂ) * A₀.coeff i ∈ Polynomial.lifts (Int.castRingHom ℂ) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro j
      rw [Polynomial.coeff_C_mul]
      by_cases hj : j ∈ (A₀.coeff i).support
      · have hi : i ∈ A₀.support := by
          rw [Polynomial.mem_support_iff]
          rintro h0
          rw [h0] at hj
          simp at hj
        obtain ⟨k, hk⟩ : (q i j).den ∣ N :=
          dvd_trans (Finset.dvd_prod_of_mem (fun j ↦ (q i j).den) hj)
            (Finset.dvd_prod_of_mem
              (fun i ↦ ∏ j ∈ (A₀.coeff i).support, (q i j).den) hi)
        refine ⟨k * (q i j).num, ?_⟩
        rw [← hq, hk, Rat.cast_def, eq_intCast]
        have hd : ((q i j).den : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (q i j).den_nz
        push_cast
        field_simp
      · rw [Polynomial.notMem_support_iff.1 hj, mul_zero]
        exact ⟨0, map_zero _⟩
    obtain ⟨r, hr⟩ := (Polynomial.mem_lifts _).1 hi
    exact ⟨r, hr⟩
  obtain ⟨A, hA⟩ := (Polynomial.mem_lifts _).1 hlift
  exact ⟨A, N, hN0, hA⟩

theorem normalize_map_ringEquiv (σ : ℂ ≃+* ℂ) (P : ℂ[X][X]) :
    normalize (P.map (Polynomial.mapRingHom (σ : ℂ →+* ℂ))) =
      (normalize P).map (Polynomial.mapRingHom (σ : ℂ →+* ℂ)) := by
  have key : ∀ Q : ℂ[X][X], normalize Q = C (C (Q.leadingCoeff.leadingCoeff)⁻¹) * Q := by
    intro Q
    by_cases hQ : Q = 0
    · simp [hQ]
    have hQ' : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hQ
    have hQ'' : Q.leadingCoeff.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hQ'
    rw [normalize_apply, Polynomial.coe_normUnit, Polynomial.coe_normUnit,
      CommGroupWithZero.coe_normUnit ℂ hQ'', mul_comm]
  have hinj : Function.Injective (Polynomial.mapRingHom (σ : ℂ →+* ℂ)) :=
    Polynomial.map_injective _ σ.injective
  rw [key, key, Polynomial.leadingCoeff_map_of_injective hinj, Polynomial.coe_mapRingHom,
    Polynomial.leadingCoeff_map_of_injective σ.injective]
  simp [Polynomial.map_mul, map_inv₀]

end AJConjecture
