import Mathlib

/-!
# The coefficient field `ℂ((h))(z)` and its first-order `q`-dilations

The local Theorem I lives over `F = ℂ((h))(z)` with the semilinear shift `σ(z) = exp(c h) z`,
`c ≠ 0`, fixing `ℂ((h))`. We realise `F` as the fraction field of `ℂ[[h]][z]` (every element of
`ℂ((h))[z]` is `h^(-n)` times an element of `ℂ[[h]][z]`, so this is `ℂ((h))(z)`), and we allow
every shift `σ(z) = Q z` with `Q = 1 + c h + O(h²)` a unit of `ℂ[[h]]` and `c ≠ 0`: all statements
depend on `Q` only through `c`, and the source's shift is `Q = exp(c h)` (`LocDilation.exp`).

Operators `∑ a_i u^i` have coefficients written on the left, `u a = σ(a) u`; the product is
`oreMul` of the library. Operators with coefficients in `ℂ[[h]][z]` are `LocOp`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The ring `ℂ[[h]][z]`: polynomials in the meridian variable `z` over `ℂ[[h]]`. -/
abbrev LocPoly : Type := (PowerSeries ℂ)[X]

/-- Operators `∑ a_i u^i` with coefficients `a_i ∈ ℂ[[h]][z]`, written on the left. -/
abbrev LocOp : Type := LocPoly[X]

/-- The coefficient field `F = ℂ((h))(z)`, the fraction field of `ℂ[[h]][z]`. -/
abbrev LocField : Type := FractionRing LocPoly

/-- The parameter `h` as a constant of `ℂ[[h]][z]`. -/
def locH : LocPoly := C PowerSeries.X

/-- A first-order `q`-dilation `σ(z) = Q z`: a unit `Q = 1 + c h + O(h²)` of `ℂ[[h]]` with
`c ≠ 0`. -/
structure LocDilation where
  /-- The multiplier `Q`. -/
  Q : (PowerSeries ℂ)ˣ
  constantCoeff_Q : PowerSeries.constantCoeff (Q : PowerSeries ℂ) = 1
  coeff_one_Q_ne_zero : PowerSeries.coeff 1 (Q : PowerSeries ℂ) ≠ 0

namespace LocDilation

/-- The first-order constant `c` of `Q = 1 + c h + O(h²)`. -/
def c (δ : LocDilation) : ℂ := PowerSeries.coeff 1 (δ.Q : PowerSeries ℂ)

theorem c_ne_zero (δ : LocDilation) : δ.c ≠ 0 := δ.coeff_one_Q_ne_zero

/-- The shift `σ(f)(h, z) = f(h, Q z)` of `ℂ[[h]][z]`. -/
def shift (δ : LocDilation) : LocPoly ≃+* LocPoly where
  toFun f := f.comp (C (δ.Q : PowerSeries ℂ) * X)
  invFun f := f.comp (C (↑δ.Q⁻¹ : PowerSeries ℂ) * X)
  left_inv f := by
    simp only [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, Units.mul_inv, C_1,
      one_mul, comp_X]
  right_inv f := by
    simp only [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, Units.inv_mul, C_1,
      one_mul, comp_X]
  map_mul' f g := mul_comp f g _
  map_add' f g := add_comp

/-- The shift as a ring endomorphism, the form taken by `oreMul`. -/
abbrev shiftHom (δ : LocDilation) : LocPoly →+* LocPoly := δ.shift.toRingHom

/-- The extension of the shift to `F = ℂ((h))(z)`. -/
def fieldShift (δ : LocDilation) : LocField ≃+* LocField :=
  IsFractionRing.ringEquivOfRingEquiv δ.shift

/-- The shift of `F` as a ring endomorphism. -/
abbrev fieldShiftHom (δ : LocDilation) : LocField →+* LocField := δ.fieldShift.toRingHom

theorem fieldShift_algebraMap (δ : LocDilation) (f : LocPoly) :
    δ.fieldShift (algebraMap LocPoly LocField f) = algebraMap LocPoly LocField (δ.shift f) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap δ.shift f

/-- `exp(c h)` is a unit of `ℂ[[h]]`. -/
theorem isUnit_rescale_exp (c : ℂ) : IsUnit (PowerSeries.rescale c (PowerSeries.exp ℂ)) := by
  apply PowerSeries.isUnit_iff_constantCoeff.2
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp]
  simp

/-- The source's dilation `σ(z) = exp(c h) z`. -/
def exp (c : ℂ) (hc : c ≠ 0) : LocDilation where
  Q := (isUnit_rescale_exp c).unit
  constantCoeff_Q := by
    rw [IsUnit.unit_spec, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
    simp
  coeff_one_Q_ne_zero := by
    rw [IsUnit.unit_spec, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
    simpa using hc

/-- The first-order constant of `exp(c h)` is `c`. -/
theorem exp_c (c : ℂ) (hc : c ≠ 0) : (exp c hc).c = c := by
  rw [LocDilation.c, exp, IsUnit.unit_spec, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp

end LocDilation

end AJConjecture
