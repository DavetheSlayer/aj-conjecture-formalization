import Mathlib
import AJConjecture.QAlgOreCoboundary
import AJConjecture.QAlgOreMonicNormalize
import AJConjecture.QAlgOreMulMap

/-!
# The coboundary identity in polynomial form, at a prime of a unique factorisation domain

Let `B` be a unique factorisation domain, `𝔭` a prime ideal, `s` an endomorphism of `B` that
extends to an automorphism `σ` of the local ring `O = B_𝔭`. If `b P = S ⋆ R` in `B[L; s]` with
`b ≠ 0` and the leading and constant coefficients of `P` outside `𝔭`, then
`r_0 γ₁ s(γ₂) v₂ = r_d v₁ s(γ₁) γ₂` with `γ₁ ≠ 0` and `γ₂, v₁, v₂ ∉ 𝔭`, where `r_0`, `r_d` are
the constant and leading coefficients of `R`.

Proof. Let `F` be the fraction field of `O` and `τ` the extension of `σ`
(`IsFractionRing.ringEquivOfRingEquiv`). Map the factorisation to `F` (`map_oreMul`), normalise
it (`exists_oreMul_monic_eq`): `r_d⁻¹ R` is a monic right factor of `p_n⁻¹ P`, which is monic
with coefficients in `O` (the leading coefficient of `P` is a unit of `O`) and unit constant
coefficient. `exists_unit_mul_coboundary_of_oreMul_eq_map` gives
`(r_0 / r_d) γ = v σ(γ)` with `v ∈ O^×`, `γ ∈ O` nonzero. Write `γ = γ₁/γ₂`, `v = v₁/v₂` with
`γ₂, v₂ ∉ 𝔭` (`IsLocalization.mk'_surjective`); `v₁ ∉ 𝔭` because `v` is a unit, `γ₁ ≠ 0`.
Clear denominators in `F` and use the injectivity of `B → F`.
-/

open Polynomial

namespace AJConjecture

/-- A coboundary relation in the local ring at a prime, with a unit factor, gives one in the base
ring: write the elements of the local ring as fractions and clear the denominators. -/
private theorem exists_coboundary_of_atPrime_relation {B : Type*} [CommRing B] [IsDomain B]
    (𝔭 : Ideal B) [𝔭.IsPrime] (s : B →+* B)
    (σ : Localization.AtPrime 𝔭 ≃+* Localization.AtPrime 𝔭)
    (hσ : ∀ a : B, σ (algebraMap B (Localization.AtPrime 𝔭) a) =
      algebraMap B (Localization.AtPrime 𝔭) (s a))
    (r₀ r₁ : B) (v : (Localization.AtPrime 𝔭)ˣ) (γ : Localization.AtPrime 𝔭) (hγ : γ ≠ 0)
    (hv : algebraMap B (Localization.AtPrime 𝔭) r₀ * γ =
      algebraMap B (Localization.AtPrime 𝔭) r₁ * (v * σ γ)) :
    ∃ γ₁ γ₂ v₁ v₂ : B, γ₁ ≠ 0 ∧ γ₂ ∉ 𝔭 ∧ v₁ ∉ 𝔭 ∧ v₂ ∉ 𝔭 ∧
      r₀ * γ₁ * s γ₂ * v₂ = r₁ * v₁ * s γ₁ * γ₂ := by
  have hι : Function.Injective (algebraMap B (Localization.AtPrime 𝔭)) :=
    IsLocalization.injective _ 𝔭.primeCompl_le_nonZeroDivisors
  obtain ⟨γ₁, γ₂, hγeq⟩ := IsLocalization.exists_mk'_eq 𝔭.primeCompl γ
  obtain ⟨v₁, v₂, hveq⟩ := IsLocalization.exists_mk'_eq 𝔭.primeCompl (v : Localization.AtPrime 𝔭)
  have hγ' : γ * algebraMap B (Localization.AtPrime 𝔭) γ₂ =
      algebraMap B (Localization.AtPrime 𝔭) γ₁ := by
    rw [← hγeq]
    exact IsLocalization.mk'_spec _ γ₁ γ₂
  have hv' : (v : Localization.AtPrime 𝔭) * algebraMap B (Localization.AtPrime 𝔭) v₂ =
      algebraMap B (Localization.AtPrime 𝔭) v₁ := by
    rw [← hveq]
    exact IsLocalization.mk'_spec _ v₁ v₂
  have hσγ : σ γ * algebraMap B (Localization.AtPrime 𝔭) (s γ₂) =
      algebraMap B (Localization.AtPrime 𝔭) (s γ₁) := by
    rw [← hσ, ← hσ, ← map_mul, hγ']
  have hγ₂ : IsUnit (algebraMap B (Localization.AtPrime 𝔭) γ₂) :=
    IsLocalization.map_units _ γ₂
  have hv₂ : IsUnit (algebraMap B (Localization.AtPrime 𝔭) v₂) :=
    IsLocalization.map_units _ v₂
  refine ⟨γ₁, γ₂, v₁, v₂, ?_, γ₂.2, ?_, v₂.2, ?_⟩
  · rintro rfl
    rw [map_zero] at hγ'
    exact hγ (hγ₂.mul_left_eq_zero.mp hγ')
  · have hunit : IsUnit (algebraMap B (Localization.AtPrime 𝔭) v₁) := by
      rw [← hv']
      exact v.isUnit.mul hv₂
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔭) 𝔭 v₁).mp hunit
  · apply hι
    simp only [map_mul]
    rw [← hγ', ← hv', ← hσγ]
    linear_combination (algebraMap B (Localization.AtPrime 𝔭) γ₂ *
      algebraMap B (Localization.AtPrime 𝔭) (s γ₂) * algebraMap B (Localization.AtPrime 𝔭) v₂) * hv

/-- The coboundary identity for the constant and leading coefficients of a right pseudo-factor,
with all terms in the base ring. -/
theorem exists_coboundary_of_oreMul_eq_of_atPrime {B : Type*} [CommRing B] [IsDomain B]
    [UniqueFactorizationMonoid B] (𝔭 : Ideal B) [𝔭.IsPrime] (s : B →+* B)
    (σ : Localization.AtPrime 𝔭 ≃+* Localization.AtPrime 𝔭)
    (hσ : ∀ a : B, σ (algebraMap B (Localization.AtPrime 𝔭) a) =
      algebraMap B (Localization.AtPrime 𝔭) (s a))
    {P S R : B[X]} {b : B} (hb : b ≠ 0) (h : C b * P = oreMul s S R)
    (hlead : P.leadingCoeff ∉ 𝔭) (hconst : P.coeff 0 ∉ 𝔭) :
    ∃ γ₁ γ₂ v₁ v₂ : B, γ₁ ≠ 0 ∧ γ₂ ∉ 𝔭 ∧ v₁ ∉ 𝔭 ∧ v₂ ∉ 𝔭 ∧
      R.coeff 0 * γ₁ * s γ₂ * v₂ = R.leadingCoeff * v₁ * s γ₁ * γ₂ := by
  have hι : Function.Injective (algebraMap B (Localization.AtPrime 𝔭)) :=
    IsLocalization.injective _ 𝔭.primeCompl_le_nonZeroDivisors
  have hκ : Function.Injective
      (algebraMap (Localization.AtPrime 𝔭) (FractionRing B)) :=
    IsFractionRing.injective _ _
  have hP : P ≠ 0 := by
    rintro rfl
    exact hlead (by rw [leadingCoeff_zero]; exact 𝔭.zero_mem)
  have hR : R ≠ 0 := by
    rintro rfl
    rw [oreMul_zero_right] at h
    exact (mul_ne_zero (C_ne_zero.mpr hb) hP) h
  obtain ⟨u, hu⟩ : IsUnit (algebraMap B (Localization.AtPrime 𝔭) P.leadingCoeff) :=
    IsLocalization.map_units _ (⟨_, hlead⟩ : 𝔭.primeCompl)
  have hu0 : IsUnit (algebraMap B (Localization.AtPrime 𝔭) (P.coeff 0)) :=
    IsLocalization.map_units _ (⟨_, hconst⟩ : 𝔭.primeCompl)
  set τ : FractionRing B →+* FractionRing B := RingEquiv.toRingHom
    (IsFractionRing.ringEquivOfRingEquiv σ : FractionRing B ≃+* FractionRing B) with hτdef
  have hτ : ∀ a : Localization.AtPrime 𝔭,
      τ (algebraMap _ (FractionRing B) a) =
        algebraMap _ (FractionRing B) (σ a) := fun a ↦
    IsFractionRing.ringEquivOfRingEquiv_algebraMap σ a
  set φ : B →+* FractionRing B :=
    (algebraMap (Localization.AtPrime 𝔭) (FractionRing B)).comp
      (algebraMap B (Localization.AtPrime 𝔭)) with hφdef
  have hφ : Function.Injective φ := hκ.comp hι
  have hφs : ∀ a, φ (s a) = τ (φ a) := by
    intro a
    rw [hφdef, RingHom.comp_apply, RingHom.comp_apply, hτ, hσ]
  have h1 : C (φ b) * P.map φ = oreMul τ (S.map φ) (R.map φ) := by
    rw [← map_oreMul φ s τ hφs, ← h, Polynomial.map_mul, map_C]
  obtain ⟨S', hS'⟩ := exists_oreMul_monic_eq τ ((map_ne_zero_iff φ hφ).mpr hb)
    ((Polynomial.map_ne_zero_iff hφ).mpr hP) h1
  rw [leadingCoeff_map_of_injective hφ, leadingCoeff_map_of_injective hφ] at hS'
  have hr : φ R.leadingCoeff ≠ 0 := (map_ne_zero_iff φ hφ).mpr (leadingCoeff_ne_zero.mpr hR)
  have hR'monic : (C (φ R.leadingCoeff)⁻¹ * R.map φ).Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [leadingCoeff_map_of_injective hφ, inv_mul_cancel₀ hr]
  have hP'monic : (C (↑u⁻¹ : Localization.AtPrime 𝔭) *
      P.map (algebraMap B (Localization.AtPrime 𝔭))).Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [leadingCoeff_map_of_injective hι, ← hu, Units.inv_mul]
  have hP'0 : IsUnit ((C (↑u⁻¹ : Localization.AtPrime 𝔭) *
      P.map (algebraMap B (Localization.AtPrime 𝔭))).coeff 0) := by
    rw [coeff_C_mul, coeff_map]
    exact u⁻¹.isUnit.mul hu0
  have hP'map : (C (↑u⁻¹ : Localization.AtPrime 𝔭) *
      P.map (algebraMap B (Localization.AtPrime 𝔭))).map
        (algebraMap _ (FractionRing B)) =
      C (φ P.leadingCoeff)⁻¹ * P.map φ := by
    rw [Polynomial.map_mul, map_C, map_map]
    congr 2
    apply eq_inv_of_mul_eq_one_left
    rw [hφdef, RingHom.comp_apply, ← hu, ← map_mul, Units.inv_mul, map_one]
  obtain ⟨v, γ, hγ, hv⟩ := exists_unit_mul_coboundary_of_oreMul_eq_map σ τ hτ hP'monic hP'0
    hR'monic (hS'.trans hP'map.symm)
  refine exists_coboundary_of_atPrime_relation 𝔭 s σ hσ _ _ v γ hγ (hκ ?_)
  rw [coeff_C_mul, coeff_map] at hv
  rw [map_mul, map_mul, ← hv]
  change φ (R.coeff 0) * _ = φ R.leadingCoeff * _
  field_simp

end AJConjecture
