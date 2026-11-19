import Mathlib
import AJConjecture.APolynomial
import AJPaper.Filling.PpAPattern
import AJPaper.Filling.PpARealize

/-!
# The generic points of `𝒫_(∓ℓ) = 0` are eigenvalue points of the twisted doubles (PpA)

Source: arXiv:2611.24826v1, Section 7.6 (`classical.tex`): "The resulting satellite
representation has the same outer eigenvalue pair, so `(L - 1) 𝒫_(-ℓ) ∣ A_S`."

* `ppa_mem_eigenvalueSet_neg`: a zero `(M, L)` of `𝒫_(-ℓ)` with `M ≠ 0`, `M⁴ ≠ 1`, `M² + L ≠ 0`
  is a point of the eigenvalue set of `W_(-,ℓ)(T(r, s)) = twWhiteheadKnot r s h ℓ true`;
* `ppa_mem_eigenvalueSet_pos`: for a zero `(M, L)` of `𝒫_ℓ` with the same conditions,
  `(M, L⁻¹)` is a point of the eigenvalue set of `W_(+,ℓ)(T(r, s)) = twWhiteheadKnot r s h ℓ
  false`.

(For `ℓ = 0` there is nothing to prove: `𝒫_0 = 1` has no zero, `twP_zero`.)

Route. Negative clasp: `ppa_exists_pattern_point (-ℓ)` gives `a`, `a₁` with
`a₁ c^(-ℓ) = c^(-ℓ) a`, `c = compMer a a₁`; so `a₁ = (c^ℓ)⁻¹ a c^ℓ` (`zpow_neg`) and `c`
satisfies the hypothesis of `ppa_exists_rep_twWhiteheadKnot_neg`, whose longitude is the pattern
longitude `a² (c^(-ℓ))⁻¹ a⁻¹ c^(-ℓ) a a₁⁻¹ a⁻¹`, upper triangular with eigenvalue `L`.
Positive clasp: `ppa_exists_pattern_point ℓ` gives `a₁ = c^ℓ a (c^ℓ)⁻¹`;
`ppa_exists_rep_twWhiteheadKnot_pos` gives a representation whose inverse longitude is the
pattern longitude; the inverse of an upper triangular element of `SL₂(ℂ)` with first diagonal
entry `L` is upper triangular with first diagonal entry `L⁻¹` (the private
`inv_entries_twCSatelliteBound` of `AJTwist.Classical.TwCSatelliteBound`).

Checked numerically: `SCR/A/py/abel2.py`, `abel3.py` (the eigenvalue of the library's longitude
on the first basis vector is a root of `𝒫_(-ℓ)(M, ·)`, resp. the inverse of a root of
`𝒫_ℓ(M, ·)`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The inverse of an upper triangular element of `SL₂(ℂ)` is upper triangular with the inverse
first diagonal entry. -/
private theorem inv_entries_ppaPoints (Y : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (h : Y.1 1 0 = 0) : (Y⁻¹).1 1 0 = 0 ∧ (Y⁻¹).1 0 0 = (Y.1 0 0)⁻¹ := by
  have hdet := Y.det_coe
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  have h11 : Y.1 1 1 = (Y.1 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  constructor
  · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, h]
  · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, h11]

/-- `𝒫_0 = 1` has no zero. -/
private theorem evalPoint_twP_zero_ne_ppaPoints (p : ℂ × ℂ) :
    evalPoint (mapC (twP 0)) p ≠ 0 := by
  simp [twP_zero, evalPoint, mapC]

/-- Negative clasp: generic zeros of `𝒫_(-ℓ)` are eigenvalue points of `W_(-,ℓ)(T(r, s))`. -/
theorem ppa_mem_eigenvalueSet_neg {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) {M L : ℂ}
    (hM : M ≠ 0) (hM4 : M ^ 4 ≠ 1) (hQ : M ^ 2 + L ≠ 0)
    (hP : evalPoint (mapC (twP (-ℓ))) (M, L) = 0) :
    (M, L) ∈ eigenvalueSet (twWhiteheadKnot r s h ℓ true) := by
  have hℓ : -ℓ ≠ 0 := fun h0 ↦ by
    rw [h0] at hP
    exact evalPoint_twP_zero_ne_ppaPoints _ hP
  obtain ⟨a, a₁, h1, h2, h3, h4, h5⟩ := ppa_exists_pattern_point (-ℓ) hℓ hM hM4 hQ hP
  rw [zpow_neg, inv_inv] at h4 h5
  have ha₁ : a₁ = (compMer a a₁ ^ ℓ)⁻¹ * a * compMer a a₁ ^ ℓ := by
    rw [zpow_neg] at h3
    rw [← h3]
    group
  obtain ⟨ρ, hm, hl⟩ := ppa_exists_rep_twWhiteheadKnot_neg h ℓ a (compMer a a₁)
    (congrArg (compMer a) ha₁)
  have hl' : ρ (longitude (twWhiteheadKnot r s h ℓ true)) =
      a ^ 2 * compMer a a₁ ^ ℓ * a⁻¹ * (compMer a a₁ ^ ℓ)⁻¹ * a * a₁⁻¹ * a⁻¹ := by
    rw [hl, ← ha₁]
  refine ⟨ρ, ?_, ?_, ?_, ?_⟩
  · rw [hm]
    exact h1
  · rw [hl']
    exact h4
  · rw [hm]
    exact h2
  · rw [hl']
    exact h5

/-- Positive clasp: generic zeros `(M, L)` of `𝒫_ℓ` give the eigenvalue points `(M, L⁻¹)` of
`W_(+,ℓ)(T(r, s))`. -/
theorem ppa_mem_eigenvalueSet_pos {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) {M L : ℂ}
    (hM : M ≠ 0) (hM4 : M ^ 4 ≠ 1) (hQ : M ^ 2 + L ≠ 0)
    (hP : evalPoint (mapC (twP ℓ)) (M, L) = 0) :
    (M, L⁻¹) ∈ eigenvalueSet (twWhiteheadKnot r s h ℓ false) := by
  have hℓ : ℓ ≠ 0 := fun h0 ↦ by
    rw [h0] at hP
    exact evalPoint_twP_zero_ne_ppaPoints _ hP
  obtain ⟨a, a₁, h1, h2, h3, h4, h5⟩ := ppa_exists_pattern_point ℓ hℓ hM hM4 hQ hP
  have ha₁ : a₁ = compMer a a₁ ^ ℓ * a * (compMer a a₁ ^ ℓ)⁻¹ := by
    rw [← h3]
    group
  obtain ⟨ρ, hm, hl⟩ := ppa_exists_rep_twWhiteheadKnot_pos h ℓ a (compMer a a₁)
    (congrArg (compMer a) ha₁)
  have hl' : ρ (longitude (twWhiteheadKnot r s h ℓ false)) =
      (a ^ 2 * (compMer a a₁ ^ ℓ)⁻¹ * a⁻¹ * compMer a a₁ ^ ℓ * a * a₁⁻¹ * a⁻¹)⁻¹ := by
    rw [← inv_inv (ρ (longitude (twWhiteheadKnot r s h ℓ false))), hl, ← ha₁]
  obtain ⟨hi1, hi2⟩ := inv_entries_ppaPoints _ h4
  refine ⟨ρ, ?_, ?_, ?_, ?_⟩
  · rw [hm]
    exact h1
  · rw [hl']
    exact hi1
  · rw [hm]
    exact h2
  · rw [hl', hi2, h5]

end AJConjecture
