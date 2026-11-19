import Mathlib
import AJHandoff.LocalTheory.LocHJet

/-!
# I-GAUGE: rescaling the parameter `h`

Under `h ↦ a h` (`a ≠ 0`, `PowerSeries.rescale a`) the shift `σ(z) = Q z` becomes
`σ(z) = Q(a h) z`, with first-order constant `a c`, and the first jet of every element is
multiplied by `a`. Both the logarithmic determinant coefficient `D₁/D₀` and the vector field
`c z d/dz` are multiplied by `a`, so the one-form `(D₁/D₀) dz/(c z)` and the normalized index are
unchanged. One must rescale both: rescaling only one of them multiplies the index by `a` or
`a⁻¹`. (A reparametrization `h ↦ a h + O(h²)` acts on first jets in the same way.)
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The dilation `σ(z) = Q(a h) z`, with first-order constant `a c`. -/
def locDilationRescale (δ : LocDilation) (a : ℂ) (ha : a ≠ 0) : LocDilation where
  Q := Units.map (PowerSeries.rescale a).toMonoidHom δ.Q
  constantCoeff_Q := by
    change PowerSeries.constantCoeff (PowerSeries.rescale a (δ.Q : PowerSeries ℂ)) = 1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
      one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, δ.constantCoeff_Q]
  coeff_one_Q_ne_zero := by
    change PowerSeries.coeff 1 (PowerSeries.rescale a (δ.Q : PowerSeries ℂ)) ≠ 0
    rw [PowerSeries.coeff_rescale, pow_one]
    exact mul_ne_zero ha δ.c_ne_zero

theorem locDilationRescale_c (δ : LocDilation) (a : ℂ) (ha : a ≠ 0) :
    (locDilationRescale δ a ha).c = a * δ.c := by
  change PowerSeries.coeff 1 (PowerSeries.rescale a (δ.Q : PowerSeries ℂ)) = a * δ.c
  rw [PowerSeries.coeff_rescale, pow_one, LocDilation.c]

/-- The substitution `h ↦ a h` on `ℂ[[h]][z]`. -/
def locRescale (a : ℂ) : LocPoly →+* LocPoly :=
  Polynomial.mapRingHom (PowerSeries.rescale a)

theorem locRescale_shift (δ : LocDilation) (a : ℂ) (ha : a ≠ 0) (f : LocPoly) :
    locRescale a (δ.shift f) = (locDilationRescale δ a ha).shift (locRescale a f) := by
  change (f.comp (C (δ.Q : PowerSeries ℂ) * X)).map (PowerSeries.rescale a) =
    (f.map (PowerSeries.rescale a)).comp (C ((locDilationRescale δ a ha).Q : PowerSeries ℂ) * X)
  rw [Polynomial.map_comp, Polynomial.map_mul, map_C, map_X]
  rfl

/-- Rescaling does not change the reduction. -/
private theorem locJet0_locRescale (a : ℂ) (f : LocPoly) :
    locJet0 (locRescale a f) = locJet0 f := by
  ext n
  rw [coeff_locJet0, coeff_locJet0, locRescale, coe_mapRingHom, coeff_map,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- Rescaling multiplies the first jet by `a`. -/
private theorem locJet1_locRescale (a : ℂ) (f : LocPoly) :
    locJet1 (locRescale a f) = C a * locJet1 f := by
  ext n
  rw [coeff_locJet1, coeff_C_mul, coeff_locJet1, locRescale, coe_mapRingHom, coeff_map,
    PowerSeries.coeff_rescale, pow_one]

/-- Rescaling `h` multiplies the first jet by `a` and keeps the normalized index. -/
theorem hasNormalizedIndex_rescale (δ : LocDilation) {a : ℂ} (ha : a ≠ 0) {A B : LocPoly}
    (hB : locJet0 B ≠ 0) {D₀ D₁ : RatFunc ℂ}
    (hD : HasHJet (algebraMap LocPoly LocField A / algebraMap LocPoly LocField B) D₀ D₁)
    {z₀ ι : ℂ} :
    HasHJet (algebraMap LocPoly LocField (locRescale a A) /
        algebraMap LocPoly LocField (locRescale a B)) D₀ (RatFunc.C a * D₁) ∧
      (HasNormalizedIndex (locDilationRescale δ a ha).c z₀ D₀ (RatFunc.C a * D₁) ι ↔
        HasNormalizedIndex δ.c z₀ D₀ D₁ ι) := by
  have hinjF := IsFractionRing.injective LocPoly LocField
  have hBF : algebraMap LocPoly LocField B ≠ 0 :=
    (map_ne_zero_iff _ hinjF).2 fun h ↦ hB (by rw [h, map_zero])
  have hrB : locJet0 (locRescale a B) ≠ 0 := by rwa [locJet0_locRescale]
  have hrBF : algebraMap LocPoly LocField (locRescale a B) ≠ 0 :=
    (map_ne_zero_iff _ hinjF).2 fun h ↦ hrB (by rw [h, map_zero])
  have h' : HasHJet (algebraMap LocPoly LocField A / algebraMap LocPoly LocField B) _ _ :=
    ⟨A, B, hB, div_mul_cancel₀ _ hBF, rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := hD.unique h'
  refine ⟨⟨locRescale a A, locRescale a B, hrB, div_mul_cancel₀ _ hrBF, ?_, ?_⟩, ?_⟩
  · rw [locJet0_locRescale, locJet0_locRescale]
  · rw [locJet0_locRescale, locJet0_locRescale, locJet1_locRescale, locJet1_locRescale,
      ← RatFunc.algebraMap_C, mul_div_assoc', ← map_mul]
    congr 2
    ring
  · unfold HasNormalizedIndex
    have ha' : (RatFunc.C a : RatFunc ℂ) ≠ 0 := by simpa using ha
    rw [locDilationRescale_c, map_mul, mul_div_assoc, mul_assoc, mul_div_mul_left _ _ ha']

end AJConjecture
