import Mathlib
import AJConjecture.ComparisonDvdDescent
import AJHandoff.TorusKnot.PairKMirrorRobust
import AJTwist.Main.TwMBarSpecialize

/-!
# From `E ∣ M^B F(M⁻¹, L)` to `E^∨ ∣ F` in the comparison ring (Unit M2)

Source: revision 5, Section 8.2 (`conclusion.tex`): "`f_{S^*}(M, L) ≐ f_S(M⁻¹, L)` … this
transports both divisibility and coprimality, with the obstruction polynomial represented by
`M⁴ E(M⁻¹, L)`."

The meridian inversion is the field automorphism `twQBar` of `ℚ(M) = RatFunc ℚ` (the same
automorphism `X ↦ X⁻¹` that is the bar involution in the variable `t`), applied to the
coefficients of polynomials in `L`.

* `twmCoeffHom`: the coefficient map `ℤ[M] → ℚ(M)` of `toComparison`;
* `twmCoeffHom_reflect`: `ψ(reflect B c) = M^B · \overline{ψ(c)}` for `deg c ≤ B`;
* `map_twmMReflect`: `M^B F(M⁻¹, L)` in `ℚ(M)[L]`;
* `twmMReflect_extraFactor`: `M⁴ E(M⁻¹, L) = E^∨` (`extraFactorMirror`);
* `twm_extraFactorMirror_dvd_of_dvd_mReflect`: if `E` divides `M^B F(M⁻¹, L)` in
  `ℚ(M)[L, L⁻¹]`, then `E^∨` divides `F` there.

Checked in exact arithmetic (`SCR/M/py/m01_mirror.py`, items (3) and (4)). This file has no
`sorry`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The coefficient map `ℤ[M] → ℚ(M)` of `toComparison`. -/
def twmCoeffHom : ℤ[X] →+* RatFunc ℚ :=
  (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem toComparison_eq_toLaurent_map (F : ℤ[X][X]) :
    toComparison F = Polynomial.toLaurent (F.map twmCoeffHom) := rfl

/-- The coefficient map is evaluation at `M`. -/
theorem twmCoeffHom_eq_eval₂ (c : ℤ[X]) :
    twmCoeffHom c = c.eval₂ (Int.castRingHom (RatFunc ℚ)) RatFunc.X := by
  rw [twmCoeffHom, RingHom.comp_apply, coe_mapRingHom, Polynomial.map, Polynomial.hom_eval₂,
    RatFunc.algebraMap_X]
  congr 1
  exact RingHom.ext_int _ _

/-- The bar of the coefficient map is evaluation at `M⁻¹`. -/
theorem twQBar_twmCoeffHom (c : ℤ[X]) :
    twQBar (twmCoeffHom c) = c.eval₂ (Int.castRingHom (RatFunc ℚ)) (RatFunc.X)⁻¹ := by
  rw [twmCoeffHom_eq_eval₂, Polynomial.hom_eval₂, twQBar_X]
  congr 1
  exact RingHom.ext_int _ _

/-- The image in `ℚ(M)` of a reflected polynomial: `M^B` times the image at `M⁻¹`. -/
theorem twmCoeffHom_reflect (B : ℕ) (c : ℤ[X]) (hc : c.natDegree ≤ B) :
    twmCoeffHom (Polynomial.reflect B c) = RatFunc.X ^ B * twQBar (twmCoeffHom c) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have : Invertible ((RatFunc.X : RatFunc ℚ)⁻¹) := invertibleOfNonzero (inv_ne_zero hX)
  have h := eval₂_reflect_mul_pow (Int.castRingHom (RatFunc ℚ)) ((RatFunc.X : RatFunc ℚ)⁻¹) B c hc
  rw [invOf_eq_inv, inv_inv] at h
  rw [twmCoeffHom_eq_eval₂, twQBar_twmCoeffHom, ← h, inv_pow, mul_comm, mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero B hX), mul_one]

/-- `M^B F(M⁻¹, L)` over `ℚ(M)`: the image of `twmMReflect B F` is `M^B` times the image of
`F` with the meridian inverted. -/
theorem map_twmMReflect (B : ℕ) (F : ℤ[X][X]) (hB : ∀ i : ℕ, (F.coeff i).natDegree ≤ B) :
    (twmMReflect B F).map twmCoeffHom =
      C ((RatFunc.X : RatFunc ℚ) ^ B) * (F.map twmCoeffHom).map twQBar := by
  ext i : 2
  rw [coeff_map, coeff_twmMReflect, coeff_C_mul, coeff_map, coeff_map,
    twmCoeffHom_reflect B _ (hB i)]

private theorem extraFactor_eq_monomials_twmReflect : extraFactor =
    monomial 2 1 + monomial 1 (-(X ^ 4 - 4 * X ^ 2 + 1)) + monomial 0 (X ^ 4) := by
  rw [extraFactor, ← C_mul_X_pow_eq_monomial, ← C_mul_X_eq_monomial, monomial_zero_left]
  simp only [map_neg, map_one]
  ring

private theorem extraFactorMirror_eq_monomials_twmReflect : extraFactorMirror =
    monomial 2 (X ^ 4) + monomial 1 (-(X ^ 4 - 4 * X ^ 2 + 1)) + monomial 0 1 := by
  rw [extraFactorMirror, ← C_mul_X_pow_eq_monomial, ← C_mul_X_eq_monomial, monomial_zero_left]
  simp only [map_neg, map_one]
  ring

/-- The coefficients of `E = L² - (M⁴ - 4M² + 1) L + M⁴` in `L`. -/
theorem coeff_extraFactor (i : ℕ) : extraFactor.coeff i =
    if i = 0 then X ^ 4 else if i = 1 then -(X ^ 4 - 4 * X ^ 2 + 1) else if i = 2 then 1
      else 0 := by
  rw [extraFactor_eq_monomials_twmReflect]
  simp only [coeff_add, coeff_monomial, Finsupp.single_apply]
  rcases i with _ | _ | _ | i <;> simp

/-- The coefficients of `E^∨ = M⁴ L² - (M⁴ - 4M² + 1) L + 1` in `L`. -/
theorem coeff_extraFactorMirror (i : ℕ) : extraFactorMirror.coeff i =
    if i = 0 then 1 else if i = 1 then -(X ^ 4 - 4 * X ^ 2 + 1) else if i = 2 then X ^ 4
      else 0 := by
  rw [extraFactorMirror_eq_monomials_twmReflect]
  simp only [coeff_add, coeff_monomial, Finsupp.single_apply]
  rcases i with _ | _ | _ | i <;> simp

/-- The coefficients of `E` have degree at most `4` in `M`. -/
theorem natDegree_coeff_extraFactor_le (i : ℕ) : (extraFactor.coeff i).natDegree ≤ 4 := by
  rw [coeff_extraFactor]
  split_ifs
  · exact natDegree_X_pow_le 4
  · rw [natDegree_neg]
    compute_degree
  · simp
  · simp

/-- `E^∨ = M⁴ E(M⁻¹, L)`: the reflection of `E` in `M` at the degree `4` is the library's
`extraFactorMirror` (defined there as `L² E(M, L⁻¹)`). -/
theorem twmMReflect_extraFactor : twmMReflect 4 extraFactor = extraFactorMirror := by
  ext i : 2
  rw [coeff_twmMReflect, coeff_extraFactor, coeff_extraFactorMirror]
  have h4 : reflect 4 (X ^ 4 : ℤ[X]) = 1 := by
    rw [reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero]
  have h2 : reflect 4 (X ^ 2 : ℤ[X]) = X ^ 2 := by
    rw [reflect_monomial, revAt_le (by norm_num)]
  have h0 : reflect 4 (1 : ℤ[X]) = X ^ 4 := by
    have := reflect_monomial (R := ℤ) 4 0
    rwa [pow_zero, revAt_le (Nat.zero_le 4)] at this
  have hmid : reflect 4 (-(X ^ 4 - 4 * X ^ 2 + 1) : ℤ[X]) = -(X ^ 4 - 4 * X ^ 2 + 1) := by
    have e : (-(X ^ 4 - 4 * X ^ 2 + 1) : ℤ[X]) =
        C (-1) * X ^ 4 + (C 4 * X ^ 2 + C (-1) * 1) := by
      simp only [map_neg, map_one, map_ofNat]
      ring
    rw [e, reflect_add, reflect_add, reflect_C_mul, reflect_C_mul, reflect_C_mul, h4, h2, h0]
    simp only [map_neg, map_one, map_ofNat]
    ring
  split_ifs
  · exact h4
  · exact hmid
  · exact h0
  · exact reflect_zero

/-- **Transport of the divisibility under the meridian inversion**: if `E` divides
`M^B F(M⁻¹, L)` in `ℚ(M)[L, L⁻¹]`, then `E^∨ = M⁴ E(M⁻¹, L)` divides `F` there. -/
theorem twm_extraFactorMirror_dvd_of_dvd_mReflect {F : ℤ[X][X]} {B : ℕ}
    (hB : ∀ i : ℕ, (F.coeff i).natDegree ≤ B)
    (h : toComparison extraFactor ∣ toComparison (twmMReflect B F)) :
    toComparison extraFactorMirror ∣ toComparison F := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h1 : extraFactor.map twmCoeffHom ∣ (twmMReflect B F).map twmCoeffHom :=
    Polynomial.map_dvd _ (extraFactor_dvd_of_toComparison_dvd h)
  rw [map_twmMReflect B F hB] at h1
  have h2 := Polynomial.map_dvd twQBar h1
  have hinv : ((F.map twmCoeffHom).map twQBar).map twQBar = F.map twmCoeffHom := by
    rw [Polynomial.map_map]
    conv_rhs => rw [← Polynomial.map_id (p := F.map twmCoeffHom)]
    congr 1
    exact RingHom.ext twQBar_twQBar
  rw [Polynomial.map_mul, Polynomial.map_C, hinv] at h2
  have h3 : extraFactorMirror.map twmCoeffHom =
      C ((RatFunc.X : RatFunc ℚ) ^ 4) * (extraFactor.map twmCoeffHom).map twQBar := by
    rw [← twmMReflect_extraFactor, map_twmMReflect 4 _ natDegree_coeff_extraFactor_le]
  have hu : IsUnit (C (twQBar ((RatFunc.X : RatFunc ℚ) ^ B)) : (RatFunc ℚ)[X]) :=
    Polynomial.isUnit_C.mpr (IsUnit.mk0 _ ((map_ne_zero twQBar).mpr (pow_ne_zero B hX)))
  have hu4 : IsUnit (C ((RatFunc.X : RatFunc ℚ) ^ 4) : (RatFunc ℚ)[X]) :=
    Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (pow_ne_zero 4 hX))
  have h4 : extraFactorMirror.map twmCoeffHom ∣ F.map twmCoeffHom := by
    rw [h3]
    exact hu4.mul_left_dvd.mpr (hu.dvd_mul_left.mp h2)
  rw [toComparison_eq_toLaurent_map, toComparison_eq_toLaurent_map]
  exact map_dvd Polynomial.toLaurent h4

end AJConjecture
