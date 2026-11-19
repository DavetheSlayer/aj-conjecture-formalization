import Mathlib
import AJConjecture.QAlgLocalizationCoboundary
import AJConjecture.QAlgNodeShiftEquiv

/-!
# The coboundary identity for a right pseudo-factor of a recurrence operator

Theorem A of the index criterion in the form used for the first jets: if `β P = S ⋆ R` in
`ℤ[t][M][L; M ↦ t² M]` and the leading and constant coefficients of `P` do not vanish at
`(t, M) = (-1, m₀)`, then over `ℂ[t][M]`
`r_0 γ₁ σ(γ₂) v₂ = r_d v₁ σ(γ₁) γ₂` with `γ₁ ≠ 0` and `γ₂`, `v₁`, `v₂` not vanishing at
`(-1, m₀)`.

Proof. Base change to `ℂ[t][M]` (`map_oreMul` with `complexShift_coeffToComplex`), then
`exists_coboundary_of_oreMul_eq_of_atPrime` for the prime `nodeIdeal m₀` and the automorphism of
`exists_ringEquiv_atPrime_nodeIdeal`; membership in `nodeIdeal m₀` is vanishing of
`(complexSpec ·).eval m₀` by definition.
-/

open Polynomial

namespace AJConjecture

/-- The base change `ℤ[t][M] → ℂ[t][M]` is injective. -/
private theorem coeffToComplex_injective_nodeCoboundary : Function.Injective coeffToComplex := by
  have h1 : Function.Injective (Polynomial.mapRingHom (Int.castRingHom ℂ)) := by
    rw [coe_mapRingHom]
    exact Polynomial.map_injective _ (RingHom.injective_int _)
  rw [coeffToComplex, coe_mapRingHom]
  exact Polynomial.map_injective _ h1

/-- The coboundary identity for the constant and leading coefficients of a right pseudo-factor
of a recurrence operator whose end coefficients do not vanish at `(-1, m₀)`. -/
theorem exists_complex_coboundary_of_pseudoFactor {m₀ : ℂ} {P S R : RecOp} {β : Coeff}
    (hβ : β ≠ 0) (h : C β * P = oreMul coeffShift S R)
    (hlead : (complexSpec (coeffToComplex P.leadingCoeff)).eval m₀ ≠ 0)
    (hconst : (complexSpec (coeffToComplex (P.coeff 0))).eval m₀ ≠ 0) :
    ∃ γ₁ γ₂ v₁ v₂ : ℂ[X][X], γ₁ ≠ 0 ∧ (complexSpec γ₂).eval m₀ ≠ 0 ∧
      (complexSpec v₁).eval m₀ ≠ 0 ∧ (complexSpec v₂).eval m₀ ≠ 0 ∧
      coeffToComplex (R.coeff 0) * γ₁ * complexShift γ₂ * v₂ =
        coeffToComplex R.leadingCoeff * v₁ * complexShift γ₁ * γ₂ := by
  have hinj := coeffToComplex_injective_nodeCoboundary
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_atPrime_nodeIdeal m₀
  have h1 : C (coeffToComplex β) * P.map coeffToComplex =
      oreMul complexShift (S.map coeffToComplex) (R.map coeffToComplex) := by
    rw [← map_oreMul coeffToComplex coeffShift complexShift
      (fun a ↦ (complexShift_coeffToComplex a).symm), ← h, Polynomial.map_mul, map_C]
  have hlead' : (P.map coeffToComplex).leadingCoeff ∉ nodeIdeal m₀ := by
    rw [leadingCoeff_map_of_injective hinj, mem_nodeIdeal_iff]
    exact hlead
  have hconst' : (P.map coeffToComplex).coeff 0 ∉ nodeIdeal m₀ := by
    rw [coeff_map, mem_nodeIdeal_iff]
    exact hconst
  obtain ⟨γ₁, γ₂, v₁, v₂, hγ₁, hγ₂, hv₁, hv₂, hc⟩ :=
    exists_coboundary_of_oreMul_eq_of_atPrime (nodeIdeal m₀) complexShift σ hσ
      ((map_ne_zero_iff coeffToComplex hinj).mpr hβ) h1 hlead' hconst'
  rw [mem_nodeIdeal_iff] at hγ₂ hv₁ hv₂
  rw [coeff_map, leadingCoeff_map_of_injective hinj] at hc
  exact ⟨γ₁, γ₂, v₁, v₂, hγ₁, hγ₂, hv₁, hv₂, hc⟩

end AJConjecture
