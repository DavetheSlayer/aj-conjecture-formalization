import Mathlib
import AJConjecture.QAlgPseudoFactorNormalize
import AJConjecture.QAlgOreMulAssoc
import AJConjecture.QAlgSpecializeNeZero
import AJConjecture.QAlgSpecializeOreMul
import AJConjecture.QAlgToComparisonUnit

/-!
# Right factors pass to the specialisation

If `β Q' = T ⋆ P₁` with `β ≠ 0` and both `Q'` and `P₁` have nonzero specialisation at `t = -1`,
then the specialisation of `P₁` divides the specialisation of `Q'` in `ℚ(M)[L, L⁻¹]`. Write
`β = (t+1)^a β'` and `T = (t+1)^b T'` with `β'`, `T'` not divisible by `t + 1`; since
`specialize` is multiplicative and `ℤ[M][L]` is a domain, `a = b`, and
`β'(-1, M) · Q'(-1) = T'(-1) · P₁(-1)` with `β'(-1, M)` a unit of the comparison ring.
-/

open Polynomial

namespace AJConjecture

/-- The specialisation of a right pseudo-factor divides the specialisation of the operator in
the comparison ring. -/
theorem toComparison_specialize_dvd_of_oreMul {Q' T P₁ : RecOp} {β : Coeff} (hβ : β ≠ 0)
    (h : C β * Q' = oreMul coeffShift T P₁) (hQ' : specialize Q' ≠ 0)
    (hP₁ : specialize P₁ ≠ 0) :
    toComparison (specialize P₁) ∣ toComparison (specialize Q') := by
  have hQ0 : Q' ≠ 0 := fun h0 ↦ hQ' (by rw [h0, map_zero])
  have hT : T ≠ 0 := by
    rintro rfl
    have hz : oreMul coeffShift (0 : RecOp) P₁ = 0 := by
      rw [← Polynomial.C_0, oreMul_C_left, Polynomial.C_0, zero_mul]
    rw [hz] at h
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hβ) hQ0 h
  obtain ⟨a, β', hβ', rfl⟩ := exists_pow_mul_map_ne_zero hβ
  obtain ⟨b, T', hT', rfl⟩ := exists_pow_mul_specialize_ne_zero hT
  have hC : C (C ((X + 1 : ℤ[X]) ^ b)) * T' = oreMul coeffShift (C (C ((X + 1 : ℤ[X]) ^ b))) T' :=
    (oreMul_C_left _ _ _).symm
  rw [hC, oreMul_assoc, oreMul_C_left, C_mul, mul_assoc] at h
  have hsU : specialize (C β' * Q') = C (β'.map (Polynomial.evalRingHom (-1 : ℤ))) *
      specialize Q' := by
    rw [map_mul]
    simp only [specialize, coe_mapRingHom, Polynomial.map_C]
  have hU : specialize (C β' * Q') ≠ 0 := by
    rw [hsU]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hβ') hQ'
  have hV : specialize (oreMul coeffShift T' P₁) ≠ 0 := by
    rw [specialize_oreMul]
    exact mul_ne_zero hT' hP₁
  have hUV := congrArg (fun p ↦ toComparison (specialize p))
    (eq_of_pow_mul_eq_pow_mul hU hV h)
  simp only [hsU, specialize_oreMul, map_mul] at hUV
  have hdvd : toComparison (specialize P₁) ∣
      toComparison (C (β'.map (Polynomial.evalRingHom (-1 : ℤ)))) *
        toComparison (specialize Q') := ⟨toComparison (specialize T'), by rw [hUV, mul_comm]⟩
  exact (isUnit_toComparison_coeff_of_ne_zero hβ').dvd_mul_left.mp hdvd

end AJConjecture
