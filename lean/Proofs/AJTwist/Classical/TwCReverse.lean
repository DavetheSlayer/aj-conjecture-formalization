import Mathlib
import AJConjecture.APolynomial
import AJConjecture.RecurrenceIdeal
import AJFamily.Classical.FamilyPolynomials
import AJHandoff.TorusKnot.PairKMirrorRobust

/-!
# Reversal in `L`: the bookkeeping of the mirror image

Source: revision 5, Section 8.2 (`conclusion.tex`, "Transport under the satellite mirror"): the
mirror image inverts one peripheral eigenvalue, `A_(S*)(M, L) ≐ A_S(M⁻¹, L)`, and the
obstruction polynomial becomes `E^∨ = M⁴ E(M⁻¹, L)`. Since eigenvalue sets are stable under
`(M, L) ↦ (M⁻¹, L⁻¹)`, inverting `M` is the same as inverting `L`, and `L ↦ L⁻¹` on
`ℤ[M][L]` is `Polynomial.reverse` up to the unit `L^deg` of the comparison ring.

* `snd_ne_zero_of_mem_eigenvalueSet`: a longitude eigenvalue is not `0`.
* `evalPoint_mapC_reverse_eq_zero_iff`: `P.reverse` vanishes at `(M, L⁻¹)` iff `P` vanishes at
  `(M, L)` (`Polynomial.eval₂_reverse_eq_zero_iff`, `Polynomial.reflect_map`).
* `toComparison_reverse`: in `ℚ(M)[L, L⁻¹]`, `P.reverse = L^(deg P) · P(L⁻¹)`
  (`LaurentPolynomial.toLaurent_reverse`; the computation is in the proof of the private
  `extraFactor_dvd_reverse_of_dvd_mirror` of `AJHandoff.TorusKnot.PairKMirrorRobust`).
* `extraFactor_reverse`: `E^∨ = extraFactorMirror` is the reverse of `E`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The first diagonal entry of an upper triangular element of `SL₂(ℂ)` is not zero. -/
private theorem entry_ne_zero_twCReverse (Y : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (h : Y.1 1 0 = 0) : Y.1 0 0 ≠ 0 := by
  have hdet := Y.det_coe
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  exact left_ne_zero_of_mul_eq_one hdet

/-- `mapC` commutes with the reverse. -/
private theorem mapC_reverse_twCReverse (P : ℤ[X][X]) : mapC P.reverse = (mapC P).reverse := by
  rw [mapC, reverse, reverse, reflect_map,
    natDegree_map_eq_of_injective (Polynomial.map_injective _ Int.cast_injective)]

/-- The longitude eigenvalue of a point of an eigenvalue set is not zero. -/
theorem snd_ne_zero_of_mem_eigenvalueSet {K : BraidKnot} {p : ℂ × ℂ}
    (hp : p ∈ eigenvalueSet K) : p.2 ≠ 0 := by
  obtain ⟨ρ, -, hl, -, hL⟩ := hp
  rw [← hL]
  exact entry_ne_zero_twCReverse _ hl

/-- The meridian eigenvalue of a point of an eigenvalue set is not zero. -/
theorem fst_ne_zero_of_mem_eigenvalueSet {K : BraidKnot} {p : ℂ × ℂ}
    (hp : p ∈ eigenvalueSet K) : p.1 ≠ 0 := by
  obtain ⟨ρ, hm, -, hM, -⟩ := hp
  rw [← hM]
  exact entry_ne_zero_twCReverse _ hm

/-- The reverse of `P` vanishes at `(M, L⁻¹)` exactly when `P` vanishes at `(M, L)`. -/
theorem evalPoint_mapC_reverse_eq_zero_iff (P : ℤ[X][X]) (M L : ℂ) (hL : L ≠ 0) :
    evalPoint (mapC P.reverse) (M, L⁻¹) = 0 ↔ evalPoint (mapC P) (M, L) = 0 := by
  have : Invertible L := invertibleOfNonzero hL
  rw [mapC_reverse_twCReverse, evalPoint, evalPoint, ← invOf_eq_inv L]
  exact eval₂_reverse_eq_zero_iff _ _ _

/-- In the comparison ring the reverse is the image under `L ↦ L⁻¹` times `L^(deg P)`. -/
theorem toComparison_reverse (P : ℤ[X][X]) :
    toComparison P.reverse =
      LaurentPolynomial.invert (toComparison P) * LaurentPolynomial.T (P.natDegree : ℤ) := by
  have hrev : (P.map ((algebraMap ℚ[X] (RatFunc ℚ)).comp
      (Polynomial.mapRingHom (Int.castRingHom ℚ)))).reverse =
      P.reverse.map ((algebraMap ℚ[X] (RatFunc ℚ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℚ))) := by
    rw [reverse, reverse, reflect_map, natDegree_map_eq_of_injective intPolyToRatFunc_injective]
  simp only [toComparison, RingHom.comp_apply, coe_mapRingHom]
  rw [← hrev, LaurentPolynomial.toLaurent_reverse,
    natDegree_map_eq_of_injective intPolyToRatFunc_injective]

/-- The mirror factor `E^∨ = M⁴ L² - (M⁴ - 4M² + 1) L + 1` is the reverse of `E`. -/
theorem extraFactor_reverse : extraFactor.reverse = extraFactorMirror := by
  have hdeg : extraFactor.natDegree = 2 := by
    rw [extraFactor]
    compute_degree!
  have hE : extraFactor = X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X ^ 1 + C (X ^ 4) := by
    rw [extraFactor, pow_one]
  rw [reverse, hdeg, hE, reflect_add, reflect_sub, reflect_monomial, reflect_C_mul_X_pow,
    reflect_C, revAt_le le_rfl, revAt_le one_le_two, extraFactorMirror]
  ring

end AJConjecture
