import Mathlib
import AJHandoff.LocalTheory.LocBasic

/-!
# The joint local ring `R₀ = ℂ[[h]][z]_(h, z - z₀)` and the hypothesis (JL)

The joint local ring at `z₀` is the localisation of `ℂ[[h]][z]` at the maximal ideal
`(h, z - z₀)`, the kernel of `f ↦ f(0, z₀)`. Every shift `σ(z) = Q z` with `Q(0) = 1` preserves
this ideal, hence acts on `R₀` (both directions). Hypothesis (JL) of the source: a semilinear
matrix lies in `GL_d(R₀)`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Evaluation `f ↦ f(0, z₀)` of `ℂ[[h]][z]`. -/
def jointEval (z₀ : ℂ) : LocPoly →+* ℂ :=
  (Polynomial.evalRingHom z₀).comp (Polynomial.mapRingHom PowerSeries.constantCoeff)

/-- The maximal ideal `(h, z - z₀)` of `ℂ[[h]][z]`. -/
def jointIdeal (z₀ : ℂ) : Ideal LocPoly := RingHom.ker (jointEval z₀)

instance jointIdeal_isPrime (z₀ : ℂ) : (jointIdeal z₀).IsPrime := RingHom.ker_isPrime _

/-- The joint local ring `R₀ = ℂ[[h]][z]_(h, z - z₀)`. -/
abbrev LocJointRing (z₀ : ℂ) : Type := Localization.AtPrime (jointIdeal z₀)

/-- The shift does not change the value at `(0, z₀)`. -/
theorem jointEval_shift (δ : LocDilation) (z₀ : ℂ) (f : LocPoly) :
    jointEval z₀ (δ.shift f) = jointEval z₀ f := by
  change eval z₀ (map PowerSeries.constantCoeff (f.comp (C (δ.Q : PowerSeries ℂ) * X))) =
    eval z₀ (map PowerSeries.constantCoeff f)
  rw [Polynomial.map_comp, Polynomial.map_mul, map_C, map_X, δ.constantCoeff_Q, C_1, one_mul,
    comp_X]

theorem map_primeCompl_jointIdeal (δ : LocDilation) (z₀ : ℂ) :
    (jointIdeal z₀).primeCompl.map δ.shift.toMonoidHom = (jointIdeal z₀).primeCompl := by
  ext x
  simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, jointIdeal, RingHom.mem_ker]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change jointEval z₀ (δ.shift y) ≠ 0
    rwa [jointEval_shift]
  · intro hx
    refine ⟨δ.shift.symm x, ?_, δ.shift.apply_symm_apply x⟩
    rwa [← jointEval_shift δ, δ.shift.apply_symm_apply]

/-- The shift of the joint local ring. -/
def locDilationJointShift (δ : LocDilation) (z₀ : ℂ) : LocJointRing z₀ ≃+* LocJointRing z₀ :=
  IsLocalization.ringEquivOfRingEquiv (LocJointRing z₀) (LocJointRing z₀) δ.shift
    (map_primeCompl_jointIdeal δ z₀)

/-- The shift of `R₀` is the restriction of the shift of `F`. -/
theorem algebraMap_jointShift (δ : LocDilation) (z₀ : ℂ) (x : LocJointRing z₀) :
    algebraMap (LocJointRing z₀) LocField (locDilationJointShift δ z₀ x) =
      δ.fieldShift (algebraMap (LocJointRing z₀) LocField x) := by
  have h : (algebraMap (LocJointRing z₀) LocField).comp (locDilationJointShift δ z₀).toRingHom =
      δ.fieldShiftHom.comp (algebraMap (LocJointRing z₀) LocField) := by
    refine IsLocalization.ringHom_ext (jointIdeal z₀).primeCompl (RingHom.ext fun f ↦ ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      locDilationJointShift, IsLocalization.ringEquivOfRingEquiv_eq]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      LocDilation.fieldShift_algebraMap]
  exact RingHom.congr_fun h x

/-- Hypothesis (JL): the matrix `A` over `F` lies in `GL_d(R₀)`. -/
def IsJointRegular (z₀ : ℂ) {d : ℕ} (A : Matrix (Fin d) (Fin d) LocField) : Prop :=
  ∃ A' : Matrix (Fin d) (Fin d) (LocJointRing z₀),
    IsUnit A'.det ∧ A = A'.map (algebraMap (LocJointRing z₀) LocField)

end AJConjecture
