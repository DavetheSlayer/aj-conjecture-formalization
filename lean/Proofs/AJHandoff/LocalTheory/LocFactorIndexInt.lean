import Mathlib
import AJConjecture.QAlgOreMonicNormalize
import AJConjecture.QAlgOreMulMap
import AJConjecture.QAlgOreMulDegree
import AJHandoff.LocalTheory.LocQuotientIndex
import AJHandoff.LocalTheory.LocCompanionQuotient
import AJHandoff.LocalTheory.LocOpJets

/-!
# The normalized index of a right factor is an integer

Let `β P = S ⋆ R` be a normalized pseudo-factorization (`β₀ ≠ 0`) of `P ∈ ℂ[[h]][z][u]` whose
residual symbol has full degree and whose leading and constant coefficients do not vanish at
`(0, z₀)`, `z₀ ≠ 0`. Then the logarithmic first jet `ν/Δ` of `r₀/r_d` has integral normalized
index at `z₀`.

Proof. Over `F`, `p_n⁻¹ P` is monic with coefficients in `R₀` and unit constant coefficient, and
`r_d⁻¹ R` is a monic right factor (`exists_oreMul_monic_eq`). The companion module of
`r_d⁻¹ R` is a quotient of that of `p_n⁻¹ P` (`oreCompanion_mul_map_oreResidueMatrix`,
`surjective_mulVecLin_oreResidueMatrix`), whose companion matrix satisfies (JL)
(`isJointRegular_oreCompanion`). Lemma 1 (`exists_hasNormalizedIndex_int_of_quotient`) applies
to `det C = (-1)^d r₀/r_d`, whose `h`-jet has `D₁/D₀ = ν/Δ`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The first jet of a sign `(-1)^m` vanishes. -/
private theorem locJet1_neg_one_pow_factorIndex (m : ℕ) : locJet1 ((-1 : LocPoly) ^ m) = 0 := by
  have h : ((-1 : LocPoly) ^ m) = C (PowerSeries.C ((-1 : ℂ) ^ m)) := by simp
  ext n
  rw [h, coeff_locJet1, coeff_C, coeff_zero]
  split_ifs
  · rw [PowerSeries.coeff_C, ite_eq_right one_ne_zero]
  · rfl

/-- The logarithmic jet of `(-1)^m r₀ / r_d` is `locLogJetNum R / locLogJetDen R`. -/
private theorem div_eq_locLogJet_of_hasHJet_factorIndex {R : LocOp}
    (hrd : locJet0 R.leadingCoeff ≠ 0) (m : ℕ) {D₀ D₁ : RatFunc ℂ}
    (h : HasHJet ((-1) ^ m * ((algebraMap LocPoly LocField R.leadingCoeff)⁻¹ *
      algebraMap LocPoly LocField (R.coeff 0))) D₀ D₁) :
    D₁ / D₀ = algebraMap ℂ[X] (RatFunc ℂ) (locLogJetNum R) /
      algebraMap ℂ[X] (RatFunc ℂ) (locLogJetDen R) := by
  have hrd' : R.leadingCoeff ≠ 0 := fun h0 ↦ hrd (by rw [h0, map_zero])
  have hι : algebraMap LocPoly LocField R.leadingCoeff ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective LocPoly LocField)).2 hrd'
  have h' : HasHJet ((-1) ^ m * ((algebraMap LocPoly LocField R.leadingCoeff)⁻¹ *
      algebraMap LocPoly LocField (R.coeff 0))) _ _ :=
    ⟨(-1) ^ m * R.coeff 0, R.leadingCoeff, hrd, by
      rw [map_mul, map_pow, map_neg, map_one]
      field_simp, rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := h.unique h'
  have hφ : algebraMap ℂ[X] (RatFunc ℂ) (locJet0 R.leadingCoeff) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).2 hrd
  have hs : ((-1 : RatFunc ℂ) ^ m) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  simp only [locLogJetNum, locLogJetDen, locJet1_mul, locJet1_neg_one_pow_factorIndex,
    map_mul, map_pow, map_neg, map_one, map_sub, zero_mul, zero_add]
  by_cases h0 : algebraMap ℂ[X] (RatFunc ℂ) (locJet0 (R.coeff 0)) = 0
  · rw [h0]
    simp
  · field_simp

/-- The monic normalisation `p_n⁻¹ P` of an operator whose leading and constant coefficients do
not vanish at `(0, z₀)` has coefficients in `R₀` and a unit constant coefficient. -/
private theorem exists_monic_jointRing_normalize_factorIndex {z₀ : ℂ} {P : LocOp}
    (hlead : jointEval z₀ P.leadingCoeff ≠ 0) (hconst : jointEval z₀ (P.coeff 0) ≠ 0) :
    ∃ P' : (LocJointRing z₀)[X], P'.Monic ∧ IsUnit (P'.coeff 0) ∧
      P'.map (algebraMap (LocJointRing z₀) LocField) =
        C (P.map (algebraMap LocPoly LocField)).leadingCoeff⁻¹ *
          P.map (algebraMap LocPoly LocField) := by
  have hinj : Function.Injective (algebraMap LocPoly (LocJointRing z₀)) :=
    IsLocalization.injective (LocJointRing z₀) (jointIdeal z₀).primeCompl_le_nonZeroDivisors
  have hmem : ∀ f : LocPoly, jointEval z₀ f ≠ 0 → f ∈ (jointIdeal z₀).primeCompl :=
    fun f hf h ↦ hf (RingHom.mem_ker.1 h)
  have hu : IsUnit (algebraMap LocPoly (LocJointRing z₀) P.leadingCoeff) :=
    IsLocalization.map_units (LocJointRing z₀) (⟨_, hmem _ hlead⟩ : (jointIdeal z₀).primeCompl)
  have hc : IsUnit (algebraMap LocPoly (LocJointRing z₀) (P.coeff 0)) :=
    IsLocalization.map_units (LocJointRing z₀) (⟨_, hmem _ hconst⟩ : (jointIdeal z₀).primeCompl)
  refine ⟨C (↑hu.unit⁻¹ : LocJointRing z₀) * P.map (algebraMap LocPoly (LocJointRing z₀)),
    ?_, ?_, ?_⟩
  · apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [leadingCoeff_map_of_injective hinj]
    exact hu.val_inv_mul
  · rw [coeff_C_mul, coeff_map]
    exact (Units.isUnit _).mul hc
  · rw [Polynomial.map_mul, map_C, Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
      leadingCoeff_map_of_injective (IsFractionRing.injective LocPoly LocField)]
    congr 2
    refine eq_inv_of_mul_eq_one_left ?_
    rw [IsScalarTower.algebraMap_apply LocPoly (LocJointRing z₀) LocField, ← map_mul,
      hu.val_inv_mul, map_one]

theorem exists_int_hasNormalizedIndex_locLogJet (δ : LocDilation) {P S R : LocOp}
    {β : LocPoly} (hβ : locJet0 β ≠ 0) (hfac : C β * P = oreMul δ.shiftHom S R) {z₀ : ℂ}
    (hz₀ : z₀ ≠ 0) (hdeg : (opJet0 P).natDegree = P.natDegree)
    (hlead : (opJet0 P).leadingCoeff.eval z₀ ≠ 0) (hconst : ((opJet0 P).coeff 0).eval z₀ ≠ 0) :
    ∃ n : ℤ, HasNormalizedIndex δ.c z₀ (algebraMap ℂ[X] (RatFunc ℂ) (locLogJetDen R))
      (algebraMap ℂ[X] (RatFunc ℂ) (locLogJetNum R)) n := by
  by_cases hrd : locJet0 R.leadingCoeff = 0
  · refine ⟨0, ?_⟩
    unfold HasNormalizedIndex HasSimpleResidue
    simp only [locLogJetDen, hrd, mul_zero, map_zero, div_zero, zero_div, Int.cast_zero,
      sub_zero]
    simpa using isRegularAt_algebraMap z₀ 0
  set ι := algebraMap LocPoly LocField
  set τ := δ.fieldShiftHom
  have hιinj : Function.Injective ι := IsFractionRing.injective LocPoly LocField
  have hτinj : Function.Injective τ := δ.fieldShift.injective
  have hP : P ≠ 0 := by
    rintro rfl
    simp [opJet0] at hlead
  have hlc : locJet0 P.leadingCoeff = (opJet0 P).leadingCoeff := by
    rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, hdeg, opJet0, coeff_map]
  have hc0 : locJet0 (P.coeff 0) = (opJet0 P).coeff 0 := by rw [opJet0, coeff_map]
  obtain ⟨P', hmon, hunit, hmap⟩ := exists_monic_jointRing_normalize_factorIndex (z₀ := z₀)
    (P := P) (by change (locJet0 _).eval z₀ ≠ 0; rwa [hlc])
    (by change (locJet0 _).eval z₀ ≠ 0; rwa [hc0])
  have hβ0 : β ≠ 0 := fun h ↦ hβ (by rw [h, map_zero])
  have hfacF : C (ι β) * P.map ι = oreMul τ (S.map ι) (R.map ι) := by
    have := congrArg (Polynomial.map ι) hfac
    rwa [map_oreMul ι δ.shiftHom τ (fun a ↦ (δ.fieldShift_algebraMap a).symm),
      Polynomial.map_mul, map_C] at this
  obtain ⟨S', hS'⟩ := exists_oreMul_monic_eq τ ((map_ne_zero_iff _ hιinj).2 hβ0)
    ((Polynomial.map_ne_zero_iff hιinj).2 hP) hfacF
  rw [← hmap] at hS'
  have hrd' : R.leadingCoeff ≠ 0 := fun h ↦ hrd (by rw [h, map_zero])
  have hRf : R.map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).2 (leadingCoeff_ne_zero.1 hrd')
  have hR'mon : (C (R.map ι).leadingCoeff⁻¹ * R.map ι).Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ (leadingCoeff_ne_zero.2 hRf))
  have hPmon : (P'.map (algebraMap (LocJointRing z₀) LocField)).Monic := hmon.map _
  have hBQ := oreCompanion_mul_map_oreResidueMatrix τ hPmon hR'mon hS'
  have hS'0 : S' ≠ 0 := by
    rintro rfl
    rw [oreMul_zero_left] at hS'
    exact hPmon.ne_zero hS'.symm
  have hle : (C (R.map ι).leadingCoeff⁻¹ * R.map ι).natDegree ≤
      (P'.map (algebraMap (LocJointRing z₀) LocField)).natDegree := by
    rw [← hS', natDegree_oreMul hτinj hS'0 hR'mon.ne_zero]
    omega
  obtain ⟨D₀, D₁, hjet, -, n, hn⟩ := exists_hasNormalizedIndex_int_of_quotient δ hz₀
    (isJointRegular_oreCompanion hmon hunit) (surjective_mulVecLin_oreResidueMatrix τ _ hle) hBQ
  refine ⟨n, ?_⟩
  rw [det_oreCompanion hR'mon, coeff_C_mul, coeff_map,
    leadingCoeff_map_of_injective hιinj] at hjet
  unfold HasNormalizedIndex at hn ⊢
  rwa [← div_eq_locLogJet_of_hasHJet_factorIndex hrd _ hjet]

end AJConjecture
