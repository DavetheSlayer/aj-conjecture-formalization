import Mathlib
import AJConjecture.ComparisonDvdDescent
import AJConjecture.ExtraFactorPrime
import AJConjecture.QAlgTwistFactorPrime
import AJConjecture.RecurrenceIdeal
import AJTwist.Factor.TwFBlockCount
import AJTwist.Factor.TwFNegFactorDegree

/-!
# Primality of `C_b` (TwF, unit F2)

Source: revision 5, Section 5.1: "This proves irreducibility of `C_b` over `ℂ(M)`"; "For `b > 1`
the degrees are `1, 2, 2b - 1`. For `b = 1`, the two linear blocks `L - 1` and `L + x³` are
distinct."

* `irreducible_twistPolyNeg_ratFunc`: `C_b` is irreducible in `ℂ(M)[L]` (`b ≥ 1`).
* `prime_toComparison_twistPolyNeg`: `C_b` is prime in the comparison ring `ℚ(M)[L, L⁻¹]`.
* `not_toComparison_dvd_twistPolyNeg`: `C_b` is associated neither to `L - 1` nor to `E` there.

Route: `irreducible_twistPoly_ratFunc` (`AJFamily/Quantum/TwistPolyIrreducible.lean`) and
`prime_toComparison_twistPoly` (`TwistPolyPrime.lean`) with `natDegree_twistPoly → 
natDegree_twistPolyNeg` (degree `2b - 1`), `two_mul_le_natDegree_of_dvd_twistPoly →
natDegree_le_of_dvd_twistPolyNeg`, `coeff_zero_twistPoly → coeff_zero_twistPolyNeg` (constant
`M^(8b-2) ≠ 0`); `C_b` is monic, so the descent from `ℂ(M)` to `ℚ(M)` is as there (the private
`ratFuncRatToComplex` of `TwistPolyPrime.lean` is restated). For the last statement compare
degrees (`natDegree_le_of_toComparison_dvd`-type bound) when `b ≥ 2` or against `E`; for `b = 1`
and `L - 1` use `C_1 = L + M⁶` (`twistPolyNeg_one`) and `C_1(M, 1) = 1 + M⁶ ≠ 0`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- `C_b` is irreducible as a polynomial in `L` over `ℂ(M)`. -/
theorem irreducible_twistPolyNeg_ratFunc (b : ℕ) (hb : 1 ≤ b) :
    Irreducible ((twistPolyNeg b).map
      ((algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)))) := by
  set φ := (algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)) with hφ
  have hinj : Function.Injective φ :=
    (IsFractionRing.injective ℂ[X] (RatFunc ℂ)).comp
      (Polynomial.map_injective _ (Int.cast_injective (α := ℂ)))
  set P := (twistPolyNeg b).map φ with hP
  have hdeg : P.natDegree = 2 * b - 1 := by
    rw [hP, Polynomial.natDegree_map_eq_of_injective hinj, natDegree_twistPolyNeg b hb]
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have hPunit : ¬ IsUnit P := by
    intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨g, hg, hgP⟩ := WfDvdMonoid.exists_irreducible_factor hPunit hP0
  have hle := natDegree_le_of_dvd_twistPolyNeg b hb hg hgP
  obtain ⟨h, hgh⟩ := hgP
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hgh
    exact hP0 hgh
  have hdegs : P.natDegree = g.natDegree + h.natDegree := by
    rw [hgh, Polynomial.natDegree_mul hg.ne_zero hh0]
  have hh : h.natDegree = 0 := by omega
  have hhu : IsUnit h := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hh]
    refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_)
    intro hc
    apply hh0
    rw [Polynomial.eq_C_of_natDegree_eq_zero hh, hc, map_zero]
  rw [hgh]
  exact (irreducible_mul_isUnit hhu).mpr hg

/-- The field embedding `ℚ(M) → ℂ(M)` induced by `ℚ → ℂ`. -/
private def ratFuncRatToComplex_twfNegPrime : RatFunc ℚ →+* RatFunc ℂ :=
  RatFunc.liftRingHom ((algebraMap ℂ[X] (RatFunc ℂ)).comp
    (Polynomial.mapRingHom (Rat.castHom ℂ))) <| by
    have hinj : Function.Injective ((algebraMap ℂ[X] (RatFunc ℂ)).comp
        (Polynomial.mapRingHom (Rat.castHom ℂ))) :=
      (IsFractionRing.injective ℂ[X] (RatFunc ℂ)).comp
        (Polynomial.map_injective _ (Rat.castHom ℂ).injective)
    intro x hx
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    exact (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hx)

/-- The embedding `ℚ(M) → ℂ(M)` is compatible with the coefficient maps from `ℤ[M]`. -/
private theorem ratFuncRatToComplex_comp_twfNegPrime :
    ratFuncRatToComplex_twfNegPrime.comp
      ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))) =
      (algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)) := by
  refine RingHom.ext fun p ↦ ?_
  simp only [ratFuncRatToComplex_twfNegPrime, RingHom.coe_comp, Function.comp_apply,
    coe_mapRingHom, RatFunc.liftRingHom_algebraMap, Polynomial.map_map]
  congr 1

/-- `C_b` is irreducible as a polynomial in `L` over `ℚ(M)`. -/
private theorem irreducible_twistPolyNeg_ratFunc_rat_twfNegPrime (b : ℕ) (hb : 1 ≤ b) :
    Irreducible ((twistPolyNeg b).map
      ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)))) := by
  have hirr := irreducible_twistPolyNeg_ratFunc b hb
  rw [← ratFuncRatToComplex_comp_twfNegPrime, ← Polynomial.map_map] at hirr
  refine Polynomial.IsPrimitive.irreducible_of_irreducible_map_of_injective
    ratFuncRatToComplex_twfNegPrime.injective ?_ hirr
  rw [Polynomial.isPrimitive_iff_ne_zero]
  exact hirr.ne_zero ∘ fun h ↦ by rw [h, Polynomial.map_zero]

/-- `C_b` is prime in the comparison ring `ℚ(M)[L, L⁻¹]`. -/
theorem prime_toComparison_twistPolyNeg (b : ℕ) (hb : 1 ≤ b) :
    Prime (toComparison (twistPolyNeg b)) := by
  refine prime_toLaurent_of_prime (irreducible_twistPolyNeg_ratFunc_rat_twfNegPrime b hb).prime ?_
  rw [coe_mapRingHom, coeff_map, coeff_zero_twistPolyNeg b hb]
  exact (map_ne_zero_iff _ intPolyToRatFunc_injective).mpr
    (pow_ne_zero _ X_ne_zero)

/-- A prime block of the comparison ring dividing `C_b` has the degree `2b - 1` of `C_b`. -/
private theorem natDegree_eq_of_prime_dvd_twistPolyNeg_twfNegPrime (b : ℕ) (hb : 1 ≤ b)
    {G : ℤ[X][X]} (hp : Prime (toComparison G)) (hc : G.coeff 0 ≠ 0)
    (h : toComparison G ∣ toComparison (twistPolyNeg b)) : G.natDegree = 2 * b - 1 := by
  have hC0 : (twistPolyNeg b).coeff 0 ≠ 0 := by
    rw [coeff_zero_twistPolyNeg b hb]
    exact pow_ne_zero _ X_ne_zero
  have hCne : twistPolyNeg b ≠ 0 := fun h0 ↦ hC0 (by rw [h0, coeff_zero])
  have hGne : G ≠ 0 := fun h0 ↦ hc (by rw [h0, coeff_zero])
  have hassoc := (hp.dvd_prime_iff_associated (prime_toComparison_twistPolyNeg b hb)).mp h
  have h1 := natDegree_le_of_toComparison_dvd hc hCne h
  have h2 := natDegree_le_of_toComparison_dvd hC0 hGne hassoc.dvd'
  rw [natDegree_twistPolyNeg b hb] at h1 h2
  omega

/-- In the comparison ring neither `L - 1` nor `E` divides `C_b`. -/
theorem not_toComparison_dvd_twistPolyNeg (b : ℕ) (hb : 1 ≤ b) :
    ¬ toComparison (X - 1) ∣ toComparison (twistPolyNeg b) ∧
      ¬ toComparison extraFactor ∣ toComparison (twistPolyNeg b) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hdeg := natDegree_eq_of_prime_dvd_twistPolyNeg_twfNegPrime b hb
      prime_toComparison_X_sub_one (by simp) h
    have hX : (X - 1 : ℤ[X][X]).natDegree = 1 := by compute_degree!
    obtain rfl : b = 1 := by omega
    have hev := eval_one_eq_zero_of_toComparison_X_sub_one_dvd h
    rw [twistPolyNeg_one] at hev
    have h0 := congrArg (Polynomial.eval 0) hev
    simp at h0
  · have hdeg := natDegree_eq_of_prime_dvd_twistPolyNeg_twfNegPrime b hb
      prime_toComparison_extraFactor (by
        rw [extraFactor_coeff_zero]
        exact pow_ne_zero 4 X_ne_zero) h
    have hE : extraFactor.natDegree = 2 := by
      rw [extraFactor]
      compute_degree!
    omega

end AJConjecture
