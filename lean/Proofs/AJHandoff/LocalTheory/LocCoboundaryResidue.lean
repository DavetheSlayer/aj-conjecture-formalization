import Mathlib
import AJHandoff.LocalTheory.LocJointRing
import AJHandoff.LocalTheory.LocHJet
import AJHandoff.LocalTheory.LocLogDerivInt

/-!
# A unit times a coboundary has an integral normalized index

Let `D = v σ(γ)/γ ∈ F` with `v` a unit of the joint local ring `R₀` at `z₀ ≠ 0` and `γ ∈ F^×`.
Then `v_h(D) = 0`, `D₀` is a unit at `z₀`, and the normalized index of `D` at `z₀` is an integer.

Proof. Write `γ = h^k γ₁/γ₂` with `γ₁, γ₂ ∈ ℂ[[h]][z]` of nonzero reduction (`h` is prime in the
unique factorisation domain `ℂ[[h]][z]` and fixed by `σ`) and `v = v₁/v₂` with
`v₁(0, z₀), v₂(0, z₀) ≠ 0`. Clearing denominators and taking jets with `locJet1_mul`,
`locJet1_shift` gives
`D₁/D₀ = (v₁)₁/(v₁)₀ - (v₂)₁/(v₂)₀ + c z ((γ₁)₀'/(γ₁)₀ - (γ₂)₀'/(γ₂)₀)`;
`pow_dvd_of_logDeriv_identity_int` with `κ = c` identifies the residue of `D₁/D₀` at `z₀` as
`c z₀ (ord (γ₁)₀ - ord (γ₂)₀)`, and division by `c z` (a unit at `z₀ ≠ 0`) gives the integer
`ord (γ₁)₀ - ord (γ₂)₀`. This is the source's `D = (σ(g)/g) V` with `j = -∑ e_β`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A nonzero element of `ℂ[[h]][z]` is `h^k γ` with `γ` of nonzero reduction. -/
private theorem exists_locH_pow_mul_locJet0_ne_zero {a : LocPoly} (ha : a ≠ 0) :
    ∃ (k : ℕ) (γ : LocPoly), locJet0 γ ≠ 0 ∧ a = locH ^ k * γ := by
  have hprime : Prime locH := Polynomial.prime_C_iff.2 PowerSeries.prime_X
  obtain ⟨k, γ, hndvd, rfl⟩ := WfDvdMonoid.max_power_factor ha hprime.irreducible
  refine ⟨k, γ, fun h0 ↦ hndvd ?_, rfl⟩
  refine (Polynomial.C_dvd_iff_dvd_coeff _ _).2 fun i ↦ PowerSeries.X_dvd_iff.2 ?_
  rw [← coeff_locJet0, h0, coeff_zero]

/-- The reduction of a shift. -/
private theorem locJet0_shift_one_cobRes (δ : LocDilation) (f : LocPoly) :
    locJet0 (δ.shift f) = locJet0 f :=
  locJet0_shift δ 1 f

/-- The first jet of a shift. -/
private theorem locJet1_shift_one_cobRes (δ : LocDilation) (f : LocPoly) :
    locJet1 (δ.shift f) = locJet1 f + C δ.c * (X * derivative (locJet0 f)) := by
  have := locJet1_shift δ 1 f
  simpa using this

/-- The normalized index of `x σ(γ₁) γ₂ / (s γ₁ σ(γ₂))` with `x(0, z₀), s(0, z₀) ≠ 0` and
`γ₁, γ₂` of nonzero reduction is the integer `ord (γ₁)₀ - ord (γ₂)₀`. -/
private theorem hasNormalizedIndex_int_of_presentation_cobRes (δ : LocDilation) {z₀ : ℂ}
    (hz₀ : z₀ ≠ 0) {D : LocField} {x s γ₁ γ₂ : LocPoly} (hx : jointEval z₀ x ≠ 0)
    (hs : jointEval z₀ s ≠ 0) (hγ₁ : locJet0 γ₁ ≠ 0) (hγ₂ : locJet0 γ₂ ≠ 0)
    (hD : D * algebraMap LocPoly LocField (s * γ₁ * δ.shift γ₂) =
      algebraMap LocPoly LocField (x * δ.shift γ₁ * γ₂)) :
    ∃ D₀ D₁ : RatFunc ℂ, HasHJet D D₀ D₁ ∧ IsUnitAt z₀ D₀ ∧
      ∃ n : ℤ, HasNormalizedIndex δ.c z₀ D₀ D₁ n := by
  have hx0 : (locJet0 x).eval z₀ ≠ 0 := hx
  have hs0 : (locJet0 s).eval z₀ ≠ 0 := hs
  have hinj := IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  have hne : ∀ p : ℂ[X], p ≠ 0 → algebraMap ℂ[X] (RatFunc ℂ) p ≠ 0 :=
    fun p hp ↦ (map_ne_zero_iff _ hinj).2 hp
  have hX0 : algebraMap ℂ[X] (RatFunc ℂ) (locJet0 x) ≠ 0 :=
    hne _ fun h ↦ hx0 (by rw [h, eval_zero])
  have hS0 : algebraMap ℂ[X] (RatFunc ℂ) (locJet0 s) ≠ 0 :=
    hne _ fun h ↦ hs0 (by rw [h, eval_zero])
  have hG1 := hne _ hγ₁
  have hG2 := hne _ hγ₂
  have hc : algebraMap ℂ[X] (RatFunc ℂ) (C δ.c) ≠ 0 := hne _ (C_ne_zero.2 δ.c_ne_zero)
  have hXX : algebraMap ℂ[X] (RatFunc ℂ) X ≠ 0 := hne _ X_ne_zero
  have hb : locJet0 (s * γ₁ * δ.shift γ₂) ≠ 0 := by
    rw [map_mul, map_mul, locJet0_shift_one_cobRes]
    exact mul_ne_zero (mul_ne_zero (fun h ↦ hs0 (by rw [h, eval_zero])) hγ₁) hγ₂
  refine ⟨_, _, ⟨_, _, hb, hD, rfl, rfl⟩, ?_, ?_⟩
  · refine ⟨locJet0 x, locJet0 s, hx0, hs0, ?_⟩
    simp only [map_mul, locJet0_shift_one_cobRes]
    field_simp
  · refine ⟨((locJet0 γ₁).rootMultiplicity z₀ : ℤ) - (locJet0 γ₂).rootMultiplicity z₀, ?_⟩
    set φ := algebraMap ℂ[X] (RatFunc ℂ)
    have hr : HasSimpleResidue (φ (locJet1 x * locJet0 s - locJet0 x * locJet1 s) /
        φ (locJet0 x * locJet0 s * (C δ.c * X))) z₀ 0 := by
      unfold HasSimpleResidue
      rw [map_zero, zero_div, sub_zero]
      refine ⟨_, _, ?_, div_mul_cancel₀ _ ?_⟩
      · simp [eval_mul, hx0, hs0, δ.c_ne_zero, hz₀]
      · simp only [map_mul]
        exact mul_ne_zero (mul_ne_zero hX0 hS0) (mul_ne_zero hc hXX)
    have h1 := hasSimpleResidue_logDeriv hγ₁ z₀
    have h2 : HasSimpleResidue (-(φ (derivative (locJet0 γ₂)) / φ (locJet0 γ₂))) z₀
        (-((locJet0 γ₂).rootMultiplicity z₀ : ℂ)) := by
      have := isRegularAt_neg (hasSimpleResidue_logDeriv hγ₂ z₀)
      unfold HasSimpleResidue
      convert this using 1
      rw [map_neg]
      ring
    have key := hr.add (h1.add h2)
    have hfun : φ (locJet1 (x * δ.shift γ₁ * γ₂) * locJet0 (s * γ₁ * δ.shift γ₂) -
          locJet0 (x * δ.shift γ₁ * γ₂) * locJet1 (s * γ₁ * δ.shift γ₂)) /
          φ (locJet0 (s * γ₁ * δ.shift γ₂)) ^ 2 /
          (φ (locJet0 (x * δ.shift γ₁ * γ₂)) / φ (locJet0 (s * γ₁ * δ.shift γ₂))) /
          (RatFunc.C δ.c * RatFunc.X) =
        φ (locJet1 x * locJet0 s - locJet0 x * locJet1 s) /
          φ (locJet0 x * locJet0 s * (C δ.c * X)) +
        (φ (derivative (locJet0 γ₁)) / φ (locJet0 γ₁) +
          -(φ (derivative (locJet0 γ₂)) / φ (locJet0 γ₂))) := by
      have hc' : (RatFunc.C δ.c : RatFunc ℂ) ≠ 0 := by simpa using δ.c_ne_zero
      have hX' : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
      simp only [φ, locJet1_mul, map_mul, locJet0_shift_one_cobRes, locJet1_shift_one_cobRes,
        map_sub, map_add, RatFunc.algebraMap_C, RatFunc.algebraMap_X] at *
      field_simp
      ring
    unfold HasNormalizedIndex
    rw [hfun]
    convert key using 1
    push_cast
    ring

theorem hasNormalizedIndex_int_of_coboundary (δ : LocDilation) {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    {D : LocField} (v : (LocJointRing z₀)ˣ) {γ : LocField} (hγ : γ ≠ 0)
    (hD : D * γ = algebraMap (LocJointRing z₀) LocField v * δ.fieldShift γ) :
    ∃ D₀ D₁ : RatFunc ℂ, HasHJet D D₀ D₁ ∧ IsUnitAt z₀ D₀ ∧
      ∃ n : ℤ, HasNormalizedIndex δ.c z₀ D₀ D₁ n := by
  obtain ⟨⟨x, t⟩, hxt⟩ := IsLocalization.mk'_surjective (jointIdeal z₀).primeCompl
    (v : LocJointRing z₀)
  dsimp only at hxt
  have hx : x ∈ (jointIdeal z₀).primeCompl := by
    rw [← IsLocalization.AtPrime.isUnit_mk'_iff (LocJointRing z₀), hxt]
    exact v.isUnit
  have hvt := IsLocalization.mk'_spec (LocJointRing z₀) x t
  rw [hxt] at hvt
  have hvt' := congrArg (algebraMap (LocJointRing z₀) LocField) hvt
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hvt'
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := LocPoly) γ
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hγ
    exact hγ rfl
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨k, γ₁, hγ₁, rfl⟩ := exists_locH_pow_mul_locJet0_ne_zero ha
  obtain ⟨l, γ₂, hγ₂, rfl⟩ := exists_locH_pow_mul_locJet0_ne_zero hb0
  refine hasNormalizedIndex_int_of_presentation_cobRes δ hz₀ hx t.2 hγ₁ hγ₂ ?_
  have hinj := IsFractionRing.injective LocPoly LocField
  have hne : ∀ p : LocPoly, p ≠ 0 → algebraMap LocPoly LocField p ≠ 0 :=
    fun p hp ↦ (map_ne_zero_iff _ hinj).2 hp
  have hH := hne locH (Polynomial.prime_C_iff.2 PowerSeries.prime_X).ne_zero
  have hG1 := hne γ₁ fun h ↦ hγ₁ (by rw [h, map_zero])
  have hG2 := hne γ₂ fun h ↦ hγ₂ (by rw [h, map_zero])
  have hG2' := hne (δ.shift γ₂) fun h ↦ hγ₂ (by rw [← locJet0_shift_one_cobRes δ, h, map_zero])
  rw [map_div₀, δ.fieldShift_algebraMap, δ.fieldShift_algebraMap] at hD
  simp only [map_mul, map_pow, (locJet_locH δ).2.2] at hD hvt' ⊢
  field_simp at hD
  rw [← hvt']
  linear_combination algebraMap LocPoly LocField (t : LocPoly) * hD

end AJConjecture
