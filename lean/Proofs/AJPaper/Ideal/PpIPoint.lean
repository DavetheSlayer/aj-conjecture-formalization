import Mathlib
import AJTwist.Main.TwMTheorem
import AJPaper.Ideal.PpITau

/-!
# Points of the extra curve outside the classical closure (Unit PpI, node `PpI_Point`)

Source: Section 8.5 of the paper (`conclusion.tex`): "By Lemma 7.1 and Theorem 1.1, a generic
point of the curve lies outside the closure of the full classical eigenvalue image … that
closure is invariant."

The classical clause of Theorem 1.1 in the library is proved from a containing polynomial
vanishing on the whole eigenvalue set; this file states that vanishing (it is used inside
`twClassClauses_twFamilyKnot_neg/_pos` but not exported) and draws the consequence for points.

* `ppi_evalPoint_twFamilyBound`: the bound of `W_(ε,ℓ)(T_η)` (`twFamilyBound σ η r s ℓ`:
  `(L - 1) 𝒫_(-ℓ) 𝒫_a` for the negative clasp, the reversed bound of the mirror knot for the
  positive clasp) vanishes at every point of the eigenvalue set. Route: the four cases of
  `AJTwist.Classical.TwCFourFamilies` with `evalPoint_twBound_of_twWhSatellite`,
  `evalPoint_twBound_of_twWhSatelliteP`, `companionDichotomyZ_torusPairKnot`,
  `isTwWhSatellite_twWhiteheadKnot`, `isTwWhSatelliteP_twWhiteheadKnot`, `isEigenMirrorOf_inv`
  and `evalPoint_mapC_reverse_eq_zero_iff`.
* `ppi_not_mem_zariskiClosure_of_bound`: every point where the bound does not vanish is outside
  the Zariski closure of the eigenvalue set. Since the bound is coprime to `G` in
  `ℚ(M)[L, L⁻¹]`, these are all points of `G = 0` outside a proper closed subset: the "generic
  points" of the paper.
* `ppi_exists_factor_zero_bound_ne_zero`: an explicit such point: `(2, L₀)` with
  `L₀² - L₀ + 16 = 0` for `E` (`evalPoint_extraFactor_witness`,
  `evalPoint_twBound_witness_ne_zero`), and `(2, L₀⁻¹)` for `E^∨`.
* `ppi_exists_point`: a point of `G = 0` with nonzero coordinates such that neither it nor its
  image under `(M, L) ↦ (M⁻¹, L⁻¹)` lies in the Zariski closure of the eigenvalue set
  (`zariskiClosure_eigenvalueSet_symm`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A bound vanishing at the points `(M, L⁻¹)` of an eigenvalue set has a reverse vanishing on
the eigenvalue set. -/
private theorem evalPoint_reverse_twBound_ppiPoint {K : BraidKnot} {k₁ k₂ : ℤ}
    (h : ∀ p ∈ eigenvalueSet K, evalPoint (mapC (twBound k₁ k₂)) (p.1, p.2⁻¹) = 0) :
    ∀ p ∈ eigenvalueSet K, evalPoint (mapC (twBound k₁ k₂).reverse) p = 0 := by
  intro p hp
  have hL : p.2⁻¹ ≠ 0 := inv_ne_zero (snd_ne_zero_of_mem_eigenvalueSet hp)
  have h1 := (evalPoint_mapC_reverse_eq_zero_iff (twBound k₁ k₂) p.1 p.2⁻¹ hL).mpr (h p hp)
  rwa [inv_inv] at h1

/-- The bound of the negative clasp vanishes on the eigenvalue set, for both companions. -/
private theorem evalPoint_twBound_negClasp_ppiPoint {r s : ℕ} (h : IsTorusPair r s) (η : Bool)
    (ℓ : ℤ) :
    ∀ p ∈ eigenvalueSet (twFamilyKnot r s h true η ℓ),
      evalPoint (mapC (twBound (-ℓ) (twIndex η r s ℓ))) p = 0 := by
  intro p hp
  cases η
  · rw [twIndex, ite_eq_right Bool.false_ne_true,
      show -((r * s : ℕ) : ℤ) - ℓ = -ℓ - ((r * s : ℕ) : ℤ) by ring]
    have h1 := evalPoint_twBound_of_twWhSatelliteP (companionDichotomyZ_torusPairKnot h)
      (isTwWhSatelliteP_twWhiteheadKnot h (-ℓ)) (isEigenMirrorOf_inv _ p hp)
    rwa [inv_inv] at h1
  · rw [twIndex, ite_eq_left rfl]
    exact evalPoint_twBound_of_twWhSatellite (companionDichotomyZ_torusPairKnot h)
      (isTwWhSatellite_twWhiteheadKnot h ℓ) hp

/-- The reversed bound of the positive clasp vanishes on the eigenvalue set, for both
companions. -/
private theorem evalPoint_twBound_posClasp_ppiPoint {r s : ℕ} (h : IsTorusPair r s) (η : Bool)
    (ℓ : ℤ) :
    ∀ p ∈ eigenvalueSet (twFamilyKnot r s h false η ℓ),
      evalPoint (mapC (twBound ℓ (-(twIndex η r s ℓ))).reverse) p = 0 := by
  refine evalPoint_reverse_twBound_ppiPoint fun p hp ↦ ?_
  cases η
  · rw [twIndex, ite_eq_right Bool.false_ne_true,
      show -(-((r * s : ℕ) : ℤ) - ℓ) = ((r * s : ℕ) : ℤ) - -ℓ by ring]
    have h1 := evalPoint_twBound_of_twWhSatellite (companionDichotomyZ_torusPairKnot h)
      (isTwWhSatellite_twWhiteheadKnot h (-ℓ)) (isEigenMirrorOf_inv _ p hp)
    rwa [neg_neg] at h1
  · rw [twIndex, ite_eq_left rfl, neg_sub]
    exact evalPoint_twBound_of_twWhSatelliteP (companionDichotomyZ_torusPairKnot h)
      (isTwWhSatelliteP_twWhiteheadKnot h ℓ) hp

/-- There is a complex number `L₀ ≠ 0` with `L₀² - L₀ + 16 = 0`. -/
private theorem exists_witness_root_ppiPoint : ∃ L : ℂ, L ≠ 0 ∧ L ^ 2 - L + 16 = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c ^ 2 = -63 := IsAlgClosed.exists_pow_nat_eq (-63) (by norm_num)
  have hL : ((1 + c) / 2) ^ 2 - (1 + c) / 2 + 16 = 0 := by linear_combination (1 / 4 : ℂ) * hc
  refine ⟨(1 + c) / 2, fun h0 ↦ ?_, hL⟩
  rw [h0] at hL
  norm_num at hL

/-- The classical bound of `W_(ε,ℓ)(T_η)` vanishes on its whole eigenvalue set. -/
theorem ppi_evalPoint_twFamilyBound {r s : ℕ} (h : IsTorusPair r s) (σ η : Bool) (ℓ : ℤ) :
    ∀ p ∈ eigenvalueSet (twFamilyKnot r s h σ η ℓ),
      evalPoint (mapC (twFamilyBound σ η r s ℓ)) p = 0 := by
  cases σ
  · exact evalPoint_twBound_posClasp_ppiPoint h η ℓ
  · exact evalPoint_twBound_negClasp_ppiPoint h η ℓ

/-- A point where the bound does not vanish is outside the Zariski closure of the eigenvalue
set. -/
theorem ppi_not_mem_zariskiClosure_of_bound {r s : ℕ} (h : IsTorusPair r s) (σ η : Bool)
    (ℓ : ℤ) {p : ℂ × ℂ} (hp : evalPoint (mapC (twFamilyBound σ η r s ℓ)) p ≠ 0) :
    p ∉ zariskiClosure (eigenvalueSet (twFamilyKnot r s h σ η ℓ)) :=
  fun hmem ↦ hp (hmem _ (ppi_evalPoint_twFamilyBound h σ η ℓ))

/-- An explicit point of the extra curve `G = 0`, with nonzero coordinates, at which the bound
does not vanish. -/
theorem ppi_exists_factor_zero_bound_ne_zero (σ η : Bool) (r s : ℕ) (ℓ : ℤ) :
    ∃ p : ℂ × ℂ, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ evalPoint (mapC (twFamilyFactor σ)) p = 0 ∧
      evalPoint (mapC (twFamilyBound σ η r s ℓ)) p ≠ 0 := by
  obtain ⟨L, hL0, hL⟩ := exists_witness_root_ppiPoint
  cases σ
  · refine ⟨(2, L⁻¹), two_ne_zero, inv_ne_zero hL0, ?_, ?_⟩
    · change evalPoint (mapC extraFactorMirror) (2, L⁻¹) = 0
      rw [← extraFactor_reverse, evalPoint_mapC_reverse_eq_zero_iff _ _ _ hL0]
      exact evalPoint_extraFactor_witness L hL
    · change evalPoint (mapC (twBound ℓ (-(twIndex η r s ℓ))).reverse) (2, L⁻¹) ≠ 0
      rw [Ne, evalPoint_mapC_reverse_eq_zero_iff _ _ _ hL0]
      exact evalPoint_twBound_witness_ne_zero L hL _ _
  · exact ⟨(2, L), two_ne_zero, hL0, evalPoint_extraFactor_witness L hL,
      evalPoint_twBound_witness_ne_zero L hL _ _⟩

/-- **A point of the extra curve outside the classical closure** (Section 8.5): a point of
`G = 0` with `M, L ≠ 0` such that neither it nor its image under the simultaneous inversion
lies in the Zariski closure of the eigenvalue set of `W_(ε,ℓ)(T_η)`. -/
theorem ppi_exists_point {r s : ℕ} (h : IsTorusPair r s) (σ η : Bool) (ℓ : ℤ) :
    ∃ p : ℂ × ℂ, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ evalPoint (mapC (twFamilyFactor σ)) p = 0 ∧
      p ∉ zariskiClosure (eigenvalueSet (twFamilyKnot r s h σ η ℓ)) ∧
      (p.1⁻¹, p.2⁻¹) ∉ zariskiClosure (eigenvalueSet (twFamilyKnot r s h σ η ℓ)) := by
  obtain ⟨p, h1, h2, hG, hB⟩ := ppi_exists_factor_zero_bound_ne_zero σ η r s ℓ
  have hp := ppi_not_mem_zariskiClosure_of_bound h σ η ℓ hB
  refine ⟨p, h1, h2, hG, hp, fun hinv ↦ hp ?_⟩
  have h3 := zariskiClosure_eigenvalueSet_symm _ (p := (p.1⁻¹, p.2⁻¹)) (inv_ne_zero h1)
    (inv_ne_zero h2) hinv
  rwa [inv_inv, inv_inv] at h3

end AJConjecture
