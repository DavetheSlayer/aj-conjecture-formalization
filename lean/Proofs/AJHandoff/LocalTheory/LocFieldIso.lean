import Mathlib
import AJHandoff.LocalTheory.LocBasic

/-!
# `F` is `ℂ((h))(z)`

The fraction field of `ℂ[[h]][z]` is canonically `RatFunc (LaurentSeries ℂ) = ℂ((h))(z)`: the
inclusion `ℂ[[h]][z] → ℂ((h))[z] → ℂ((h))(z)` is injective, and every element of `ℂ((h))(z)` is a
quotient of two elements of `ℂ((h))[z]`, each `h^(-n)` times an element of `ℂ[[h]][z]`. This
justifies the realisation `LocField` of the source's coefficient field.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Polynomials over `ℂ((h))`, with the semiring structure coming from the field `ℂ((h))`. -/
private abbrev LaurentPolyIso : Type :=
  @Polynomial (LaurentSeries ℂ) (@CommSemiring.toSemiring _ CommRing.toCommSemiring)

/-- The inclusion `ℂ[[h]] → ℂ((h))`. -/
private def powerSeriesToLaurentIso : @RingHom (PowerSeries ℂ) (LaurentSeries ℂ) _
    (@CommSemiring.toSemiring _ CommRing.toCommSemiring).toNonAssocSemiring :=
  HahnSeries.ofPowerSeries ℤ ℂ

/-- The inclusion `ℂ[[h]][z] → ℂ((h))(z)`. -/
private def locToRatFuncLaurent : LocPoly →+* RatFunc (LaurentSeries ℂ) :=
  (algebraMap LaurentPolyIso (RatFunc (LaurentSeries ℂ))).comp
    (Polynomial.mapRingHom powerSeriesToLaurentIso)

/-- The inclusion on an element. -/
private theorem locToRatFuncLaurent_apply (f : LocPoly) :
    locToRatFuncLaurent f = algebraMap LaurentPolyIso (RatFunc (LaurentSeries ℂ))
      (f.map powerSeriesToLaurentIso) :=
  rfl

/-- The inclusion is injective. -/
private theorem locToRatFuncLaurent_injective : Function.Injective locToRatFuncLaurent := by
  intro a b hab
  rw [locToRatFuncLaurent_apply, locToRatFuncLaurent_apply] at hab
  exact Polynomial.map_injective _ HahnSeries.ofPowerSeries_injective
    (IsFractionRing.injective LaurentPolyIso (RatFunc (LaurentSeries ℂ)) hab)

/-- Every polynomial over `ℂ((h))` is a polynomial over `ℂ[[h]]` divided by a nonzero constant. -/
private theorem exists_C_mul_eq_map_fieldIso (p : LaurentPolyIso) :
    ∃ b : PowerSeries ℂ, b ≠ 0 ∧ ∃ q : LocPoly,
      C (powerSeriesToLaurentIso b) * p = q.map powerSeriesToLaurentIso := by
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (PowerSeries ℂ)) p
  refine ⟨b, nonZeroDivisors.ne_zero hb,
    IsLocalization.integerNormalization (nonZeroDivisors (PowerSeries ℂ)) p, ?_⟩
  change _ = Polynomial.map (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)) _
  rw [hq, ← algebraMap_smul (LaurentSeries ℂ) b p, smul_eq_C_mul]
  rfl

/-- Every element of `ℂ((h))(z)` is a quotient of elements of `ℂ[[h]][z]`. -/
private theorem locToRatFuncLaurent_surj (z : RatFunc (LaurentSeries ℂ)) :
    ∃ x y : LocPoly, z = locToRatFuncLaurent x / locToRatFuncLaurent y := by
  set ι : LaurentPolyIso →+* RatFunc (LaurentSeries ℂ) :=
    algebraMap LaurentPolyIso (RatFunc (LaurentSeries ℂ))
  have hinj : Function.Injective ι := IsFractionRing.injective _ _
  obtain ⟨b₁, hb₁, q₁, h₁⟩ := exists_C_mul_eq_map_fieldIso z.num
  obtain ⟨b₂, hb₂, q₂, h₂⟩ := exists_C_mul_eq_map_fieldIso z.denom
  have hB : ∀ b : PowerSeries ℂ, b ≠ 0 → ι (C (powerSeriesToLaurentIso b)) ≠ 0 :=
    fun b hb ↦ (map_ne_zero_iff _ hinj).2
      (C_ne_zero.2 ((map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).2 hb))
  have hD : ι z.denom ≠ 0 := (map_ne_zero_iff _ hinj).2 z.denom_ne_zero
  refine ⟨q₁ * C b₂, q₂ * C b₁, ?_⟩
  simp only [locToRatFuncLaurent_apply, map_C, map_mul, ← h₁, ← h₂]
  have hB₁ := hB b₁ hb₁
  have hB₂ := hB b₂ hb₂
  have hz : z = ι z.num / ι z.denom := (RatFunc.num_div_denom z).symm
  conv_lhs => rw [hz]
  rw [div_eq_div_iff hD (mul_ne_zero (mul_ne_zero hB₂ hD) hB₁)]
  ring

theorem exists_ringEquiv_locField_ratFunc :
    ∃ e : LocField ≃+* RatFunc (LaurentSeries ℂ), ∀ f : LocPoly,
      e (algebraMap LocPoly LocField f) =
        ((f.map (HahnSeries.ofPowerSeries ℤ ℂ) : (LaurentSeries ℂ)[X]) :
          RatFunc (LaurentSeries ℂ)) := by
  let _ : Algebra LocPoly (RatFunc (LaurentSeries ℂ)) := locToRatFuncLaurent.toAlgebra
  have : FaithfulSMul LocPoly (RatFunc (LaurentSeries ℂ)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 locToRatFuncLaurent_injective
  have : IsFractionRing LocPoly (RatFunc (LaurentSeries ℂ)) :=
    IsFractionRing.of_field _ _ locToRatFuncLaurent_surj
  refine ⟨(IsLocalization.algEquiv (nonZeroDivisors LocPoly) LocField
    (RatFunc (LaurentSeries ℂ))).toRingEquiv, fun f ↦ ?_⟩
  rw [AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes]
  rfl

end AJConjecture
