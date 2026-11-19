import Mathlib
import AJConjecture.QAlgOreMulZero

/-!
# Monic normalisation of a pseudo-factorisation over a field

From `b P = S ⋆ R` over a field, with `b ≠ 0` and `P ≠ 0`: the monic operator
`R' = r_d⁻¹ R` is a right factor of the monic operator `p_n⁻¹ P`. With
`S' = C (p_n⁻¹ b⁻¹) * (S ⋆ C r_d)`:
`S' ⋆ R' = C (p_n⁻¹ b⁻¹) * (S ⋆ (C r_d ⋆ (C r_d⁻¹ * R))) = C (p_n⁻¹ b⁻¹) * (S ⋆ R)`
by `C_mul_oreMul`, `oreMul_assoc` and `oreMul_C_left`.
-/

open Polynomial

namespace AJConjecture

/-- The monic normalisation of a right pseudo-factor is a right factor of the monic
normalisation. -/
theorem exists_oreMul_monic_eq {F : Type*} [Field F] (τ : F →+* F) {P S R : F[X]} {b : F}
    (hb : b ≠ 0) (hP : P ≠ 0) (h : C b * P = oreMul τ S R) :
    ∃ S' : F[X], oreMul τ S' (C R.leadingCoeff⁻¹ * R) = C P.leadingCoeff⁻¹ * P := by
  have hR : R ≠ 0 := by
    rintro rfl
    rw [oreMul_zero_right] at h
    exact (mul_ne_zero (C_ne_zero.mpr hb) hP) h
  have hr : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR
  refine ⟨C (P.leadingCoeff⁻¹ * b⁻¹) * oreMul τ S (C R.leadingCoeff), ?_⟩
  rw [← C_mul_oreMul, oreMul_assoc, oreMul_C_left, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hr, C_1,
    one_mul, ← h, ← mul_assoc, ← C_mul, mul_assoc, inv_mul_cancel₀ hb, mul_one]

end AJConjecture
