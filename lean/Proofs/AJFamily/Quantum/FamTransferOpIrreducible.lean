import Mathlib
import AJConjecture.ComparisonDvdDescent
import AJFamily.Quantum.AbNodeNoSeparation
import AJFamily.Quantum.EbNodeNoSeparation

/-!
# The family transfer operator has no proper right factor

`natDegree_eq_zero_or_of_oreMul_eq_famTransferOp`: for `m ≥ 2`, a right factor of
`famTransferOp m` has degree `0` or `2m + 3`. The prime factors `L - 1`, `E`, `B_m` of the symbol
are not separated at the two nodes, so the symbol of a right factor contains all of them or
none.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- Divisibility in the comparison ring by the image of a polynomial with nonzero constant
coefficient bounds the degree in `L`. -/
private theorem natDegree_le_of_toComparison_dvd_famIrred {d g : ℤ[X][X]}
    (hd : d.coeff 0 ≠ 0) (hg : g ≠ 0) (h : toComparison d ∣ toComparison g) :
    d.natDegree ≤ g.natDegree := by
  have hdvd : d.map ((algebraMap ℚ[X] (RatFunc ℚ)).comp
      (Polynomial.mapRingHom (Int.castRingHom ℚ))) ∣ g.map ((algebraMap ℚ[X] (RatFunc ℚ)).comp
      (Polynomial.mapRingHom (Int.castRingHom ℚ))) := by
    refine dvd_of_toLaurent_dvd ?_ h
    rw [coeff_map]
    exact (map_ne_zero_iff _ intPolyToRatFunc_injective).mpr hd
  have hle := natDegree_le_of_dvd hdvd
    ((Polynomial.map_ne_zero_iff intPolyToRatFunc_injective).mpr hg)
  rwa [natDegree_map_eq_of_injective intPolyToRatFunc_injective,
    natDegree_map_eq_of_injective intPolyToRatFunc_injective] at hle

/-- The constant coefficient of `L - 1` is `-1`. -/
private theorem coeff_zero_X_sub_one_famIrred : (X - 1 : ℤ[X][X]).coeff 0 = -1 := by
  simp

/-- A nonzero polynomial whose image in the comparison ring is divisible by `L - 1`, `E` and
`B_m` has degree at least `2m + 3` in `L`. -/
private theorem le_natDegree_of_dvd_famIrred (m : ℕ) (hm : 2 ≤ m) {g : ℤ[X][X]} (hg : g ≠ 0)
    (h1 : toComparison (X - 1) ∣ toComparison g)
    (h2 : toComparison extraFactor ∣ toComparison g)
    (h3 : toComparison (twistPoly m) ∣ toComparison g) : 2 * m + 3 ≤ g.natDegree := by
  have hX0 : (X - 1 : ℤ[X][X]) ≠ 0 := fun h0 ↦ by
    simpa [h0] using natDegree_X_sub_one
  have hE0 : extraFactor ≠ 0 := fun h0 ↦ by
    simpa [h0] using natDegree_extraFactor
  have hB0 : twistPoly m ≠ 0 := fun h0 ↦ by
    have := natDegree_twistPoly m
    rw [h0, natDegree_zero] at this
    omega
  have hEc : extraFactor.coeff 0 ≠ 0 := by
    rw [extraFactor_coeff_zero]
    exact pow_ne_zero 4 X_ne_zero
  have hBc : (twistPoly m).coeff 0 ≠ 0 := by
    rw [coeff_zero_twistPoly]
    exact pow_ne_zero _ X_ne_zero
  obtain ⟨q₁, hq₁⟩ := h1
  have h2' : toComparison extraFactor ∣ q₁ := by
    rw [hq₁] at h2
    refine (prime_toComparison_extraFactor.dvd_or_dvd h2).resolve_left fun hdvd ↦ ?_
    have hle := natDegree_le_of_toComparison_dvd_famIrred hEc hX0 hdvd
    rw [natDegree_extraFactor, natDegree_X_sub_one] at hle
    omega
  obtain ⟨q₂, rfl⟩ := h2'
  have h3' : toComparison (twistPoly m) ∣ q₂ := by
    rw [hq₁] at h3
    rcases (prime_toComparison_twistPoly m hm).dvd_or_dvd h3 with hdvd | hdvd
    · have hle := natDegree_le_of_toComparison_dvd_famIrred hBc hX0 hdvd
      rw [natDegree_twistPoly, natDegree_X_sub_one] at hle
      omega
    · refine ((prime_toComparison_twistPoly m hm).dvd_or_dvd hdvd).resolve_left
        fun hdvd' ↦ ?_
      have hle := natDegree_le_of_toComparison_dvd_famIrred hBc hE0 hdvd'
      rw [natDegree_twistPoly, natDegree_extraFactor] at hle
      omega
  obtain ⟨q₃, rfl⟩ := h3'
  have hall : toComparison ((X - 1) * extraFactor * twistPoly m) ∣ toComparison g := by
    rw [hq₁, map_mul, map_mul]
    exact ⟨q₃, by ring⟩
  have hc : ((X - 1) * extraFactor * twistPoly m : ℤ[X][X]).coeff 0 ≠ 0 := by
    rw [mul_coeff_zero, mul_coeff_zero, coeff_zero_X_sub_one_famIrred]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr one_ne_zero) hEc) hBc
  have hle := natDegree_le_of_toComparison_dvd_famIrred hc hg hall
  rw [natDegree_mul (mul_ne_zero hX0 hE0) hB0, natDegree_mul hX0 hE0,
    natDegree_X_sub_one, natDegree_extraFactor,
    natDegree_twistPoly] at hle
  omega

/-- Each divisor of `(L - 1) E B_m` divides the symbol of `famTransferOp m` in the comparison
ring. -/
private theorem toComparison_dvd_specialize_famTransferOp_famIrred (m : ℕ) (hm : 1 ≤ m)
    {p : ℤ[X][X]} (hp : p ∣ (X - 1) * extraFactor * twistPoly m) :
    toComparison p ∣ toComparison (specialize (famTransferOp m)) := by
  have hκ : ((X ^ 2 - 1) ^ (2 * m + 3) * (X ^ 4 - 1) ^ (2 * m + 3) : ℤ[X]) ≠ 0 := by
    have h2 : (X ^ 2 - 1 : ℤ[X]) ≠ 0 := by
      simpa using (monic_X_pow_sub_C (1 : ℤ) (two_ne_zero)).ne_zero
    have h4 : (X ^ 4 - 1 : ℤ[X]) ≠ 0 := by
      simpa using (monic_X_pow_sub_C (1 : ℤ) (four_ne_zero)).ne_zero
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h4)
  have hsym : toComparison (C ((X ^ 2 - 1) ^ (2 * m + 3) * (X ^ 4 - 1) ^ (2 * m + 3))) *
      toComparison (specialize (famTransferOp m)) =
      toComparison (C ((famDet m (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1)))) *
        toComparison ((X - 1) * extraFactor * twistPoly m) := by
    rw [← map_mul, ← map_mul, specialize_famTransferOp_mul_eq m hm]
  rw [← (isUnit_toComparison_coeff_of_ne_zero hκ).dvd_mul_left, hsym]
  exact (map_dvd toComparison hp).mul_left _

/-- The family operator `famTransferOp m` (`m ≥ 2`) has no proper right factor over `ℚ(t, M)`:
in every pseudo-factorisation `β · famTransferOp m = S ⋆ R` the right factor has degree `0` or
`2m + 3`. -/
theorem natDegree_eq_zero_or_of_oreMul_eq_famTransferOp (m : ℕ) (hm : 2 ≤ m) {β : Coeff}
    (hβ : β ≠ 0) {S R : RecOp} (h : C β * famTransferOp m = oreMul coeffShift S R) :
    R.natDegree = 0 ∨ R.natDegree = 2 * m + 3 := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨β', S', R', hβ', hS', hR', -, hRdeg, h', -⟩ :=
    exists_normalized_pseudoFactor (specialize_famTransferOp_ne_zero m hm1) hβ h
  have hβ'0 : β' ≠ 0 := fun h0 ↦ hβ' (by rw [h0, Polynomial.map_zero])
  have hS'0 : S' ≠ 0 := fun h0 ↦ hS' (by rw [h0, map_zero])
  have hR'0 : R' ≠ 0 := fun h0 ↦ hR' (by rw [h0, map_zero])
  have hsp : C (β'.map (Polynomial.evalRingHom (-1 : ℤ))) * specialize (famTransferOp m) =
      specialize S' * specialize R' := by
    have hC : specialize (C β') = C (β'.map (Polynomial.evalRingHom (-1 : ℤ))) :=
      Polynomial.map_C _
    rw [← specialize_oreMul, ← h', map_mul, hC]
  have hdegOre : S'.natDegree + R'.natDegree = 2 * m + 3 := by
    rw [← natDegree_oreMul coeffShift_injective hS'0 hR'0, ← h', natDegree_C_mul hβ'0,
      natDegree_famTransferOp m hm1]
  have hdeg₀ : (specialize S').natDegree + (specialize R').natDegree = 2 * m + 3 := by
    rw [← natDegree_mul hS' hR', ← hsp, natDegree_C_mul hβ',
      natDegree_specialize_famTransferOp m hm1]
  have hSle : (specialize S').natDegree ≤ S'.natDegree := natDegree_map_le
  have hRle : (specialize R').natDegree ≤ R'.natDegree := natDegree_map_le
  have hprod : ∀ {p : ℤ[X][X]}, p ∣ (X - 1) * extraFactor * twistPoly m →
      toComparison p ∣ toComparison (specialize S') * toComparison (specialize R') := by
    intro p hp
    rw [← map_mul, ← hsp, map_mul]
    exact (toComparison_dvd_specialize_famTransferOp_famIrred m hm1 hp).mul_left _
  have h13 := toComparison_X_sub_one_dvd_iff_twistPoly_dvd m hm hβ'0 h'
  have h23 := toComparison_extraFactor_dvd_iff_twistPoly_dvd m hm hβ'0 h'
  by_cases h3 : toComparison (twistPoly m) ∣ toComparison (specialize R')
  · right
    have hle := le_natDegree_of_dvd_famIrred m hm hR' (h13.mpr h3) (h23.mpr h3) h3
    omega
  · left
    have hS1 := (prime_toComparison_X_sub_one.dvd_or_dvd (hprod ⟨extraFactor * twistPoly m,
      by ring⟩)).resolve_right fun hdvd ↦ h3 (h13.mp hdvd)
    have hS2 := (prime_toComparison_extraFactor.dvd_or_dvd (hprod ⟨(X - 1) * twistPoly m,
      by ring⟩)).resolve_right fun hdvd ↦ h3 (h23.mp hdvd)
    have hS3 := ((prime_toComparison_twistPoly m hm).dvd_or_dvd (hprod ⟨(X - 1) * extraFactor,
      by ring⟩)).resolve_right h3
    have hle := le_natDegree_of_dvd_famIrred m hm hS' hS1 hS2 hS3
    omega

end AJConjecture
