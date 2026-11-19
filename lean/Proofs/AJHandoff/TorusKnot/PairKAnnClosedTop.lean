import Mathlib
import AJHandoff.TorusKnot.PairKAnnFrame

/-!
# The closed forms solve the band equations of the rounds

The edge meridians `pairAnnEdge r s y a` satisfy the round transitions required by
`AJHandoff.TorusKnot.PairKAnnEqTop`. Every round transition is `Φ e Φ⁻¹` with `Φ = R' Π⁻¹`, i.e.
`R' (Π⁻¹ e Π) R'⁻¹` (by `group`), a move `pairAnnForm_conjP` (`w ↦ w - 1`) followed by
`pairAnnForm_conj` in the frame of the upper level (`pairAnnHur_eq_top`):

* `R_0`: `T_r` has `w = h(r) = 1`, `l = -1`, `k = -2`, `T_0` has `w = 0`, `k = l = 0`
  (`pairAnn_ends`, `pairAnn_lab_top`); `R'_(s-1)` in the frame of `T_0` (`s - 1 ≡ -1`); after the
  conjugation one more `pairAnnForm_left`;
* `R_τ`, `1 ≤ τ ≤ s - 2`: `h(τ + r) = h(τ) + 1`, `i(τ + r) = i(τ)` (`pairAnn_chain`), so
  `l(T_(τ+r)) = l(T_τ) - 1`; `R'_(τ-1)` in the frame of `T_τ`;
* `R_(s-1)`: the lower run level `r - 2` has `w = h(r - 1) = h(s - 1) + 1`, `k = l = l(T_(s-1)) - 2`
  (`pairAnn_lab_low`, `pairAnn_run`); `R'_(s-2)` in the frame of `T_(s-1)`; after the conjugation
  one more `pairAnnForm_right`.

Route as in `AJHandoff.TorusKnot.PairKAnnClosedLow`. Checked exactly
(`SCR/ANN/check_closed.py`).
-/

namespace AJConjecture

variable {G : Type*} [Group G] {r s : ℕ}

/-- `Φ x Φ⁻¹ = R (Π⁻¹ x Π) R⁻¹` for `Φ = R Π⁻¹`. -/
private theorem pairAnn_phi_conj (R P x : G) :
    (R * P⁻¹) * x * (R * P⁻¹)⁻¹ = R * (P⁻¹ * x * P) * R⁻¹ := by
  group

/-- `R_0`: `e(T_0) = R'_(s-1) Φ₀ e(T_r) Φ₀⁻¹`, `Φ₀ = R'_(s-1) Π⁻¹`. -/
theorem pairAnnEdge_R0 (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (a : G) :
    pairAnnEdge r s y a (2 * pairC r s - 1) =
      pairAnnHur r y (s - 1) * (pairAnnHur r y (s - 1) * (pairAnnPi r y)⁻¹) *
        pairAnnEdge r s y a (2 * pairC r s - 1 - r) *
        (pairAnnHur r y (s - 1) * (pairAnnPi r y)⁻¹)⁻¹ := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  obtain ⟨hW1, hL1, hP1⟩ := pairAnn_lab_top h (t := 0) (by omega)
  obtain ⟨hW2, hL2, hP2⟩ := pairAnn_lab_top h (t := r) (by omega)
  obtain ⟨hh0, hl0, hhr, hlr, -, -⟩ := pairAnn_ends h
  rw [Nat.sub_zero] at hW1 hL1 hP1
  rw [ite_eq_left rfl] at hP1
  rw [ite_eq_right (by omega)] at hP2
  have hR := pairAnnHur_eq_top h y hy 0 (s - 1) (by
    rw [Int.modEq_iff_dvd]; exact ⟨-1, by omega⟩)
  rw [mul_assoc (pairAnnHur r y (s - 1)), mul_assoc (pairAnnHur r y (s - 1)), pairAnn_phi_conj]
  simp only [pairAnnEdge, pairAnnKap, hW1, hL1, hP1, hW2, hL2, hP2]
  rw [pairAnnForm_conjP, show pairAnnTopW r s r - pairAnnW r s 0 - 1 =
      pairAnnTopW r s 0 - pairAnnW r s 0 by simp only [pairAnnTopW, hh0, hhr]; push_cast; ring,
    pairAnnForm_conj hR, pairAnnForm_left hR, hl0, hlr]
  congr 1 <;> ring

/-- `R_τ`, `1 ≤ τ ≤ s - 2`: `e(T_τ) = Φ_τ e(T_(r+τ)) Φ_τ⁻¹`, `Φ_τ = R'_(τ-1) Π⁻¹`. -/
theorem pairAnnEdge_R (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (a : G) (τ : ℕ) (h1 : 1 ≤ τ) (h2 : τ ≤ s - 2) :
    pairAnnEdge r s y a (2 * pairC r s - 1 - τ) =
      (pairAnnHur r y (τ - 1) * (pairAnnPi r y)⁻¹) *
        pairAnnEdge r s y a (2 * pairC r s - 1 - r - τ) *
        (pairAnnHur r y (τ - 1) * (pairAnnPi r y)⁻¹)⁻¹ := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  obtain ⟨hW1, hL1, hP1⟩ := pairAnn_lab_top h (t := τ) (by omega)
  obtain ⟨hW2, hL2, hP2⟩ := pairAnn_lab_top h (t := τ + r) (by omega)
  obtain ⟨hi, hht⟩ := pairAnn_chain h τ
  rw [ite_eq_right (by omega)] at hP1 hP2
  rw [show 2 * pairC r s - 1 - (τ + r) = 2 * pairC r s - 1 - r - τ by omega] at hW2 hL2 hP2
  have hR := pairAnnHur_eq_top h y hy τ (τ - 1) (by
    rw [Int.modEq_iff_dvd]; exact ⟨0, by omega⟩)
  rw [pairAnn_phi_conj]
  simp only [pairAnnEdge, pairAnnKap, hW1, hL1, hP1, hW2, hL2, hP2]
  rw [pairAnnForm_conjP, show pairAnnTopW r s (τ + r) - pairAnnW r s 0 - 1 =
      pairAnnTopW r s τ - pairAnnW r s 0 by simp only [pairAnnTopW, hht]; push_cast; ring,
    pairAnnForm_conj hR]
  congr 1 <;> simp only [pairAnnTopL, hi, hht] <;> push_cast <;> ring

/-- `R_(s-1)`: `e(T_(s-1)) = Φ e(r - 2) Φ⁻¹ R'_(s-2)⁻¹`, `Φ = R'_(s-2) Π⁻¹`. -/
theorem pairAnnEdge_Rlast (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (a : G) :
    pairAnnEdge r s y a (2 * pairC r s - s) =
      (pairAnnHur r y (s - 2) * (pairAnnPi r y)⁻¹) * pairAnnEdge r s y a (r - 2) *
        (pairAnnHur r y (s - 2) * (pairAnnPi r y)⁻¹)⁻¹ * (pairAnnHur r y (s - 2))⁻¹ := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  obtain ⟨hW1, hL1, hP1⟩ := pairAnn_lab_top h (t := s - 1) (by omega)
  obtain ⟨hW2, hL2, hP2⟩ := pairAnn_lab_low h (n := r - 2) le_rfl (by omega)
  obtain ⟨hH, -⟩ := pairAnn_run h
  rw [show 2 * pairC r s - 1 - (s - 1) = 2 * pairC r s - s by omega] at hW1 hL1 hP1
  rw [ite_eq_right (by omega)] at hP1
  have hR := pairAnnHur_eq_top h y hy (s - 1) (s - 2) (by
    rw [Int.modEq_iff_dvd]; exact ⟨0, by omega⟩)
  rw [pairAnn_phi_conj]
  simp only [pairAnnEdge, pairAnnKap, hW1, hL1, hP1, hW2, hL2, hP2]
  rw [pairAnnForm_conjP, show pairAnnTopW r s (r - 1) - pairAnnW r s 0 - 1 =
      pairAnnTopW r s (s - 1) - pairAnnW r s 0 by simp only [pairAnnTopW, hH]; push_cast; ring,
    pairAnnForm_conj hR, pairAnnForm_right hR]
  congr 1 <;> ring

end AJConjecture
