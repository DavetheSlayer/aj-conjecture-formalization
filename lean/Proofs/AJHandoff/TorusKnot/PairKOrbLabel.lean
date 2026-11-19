import Mathlib
import AJHandoff.TorusKnot.PairKOrbRounds

/-!
# The label congruence

Off the strand `pairOrbH1`, the label of a position and the label of its image under the strand
map satisfy `ℓ(t) ≡ ℓ(P t) + r w(t) (mod s)`; hence `y_(ℓ t) = K ^ w(t) y_(ℓ(P t)) K ^ (-w(t))`,
which is what makes pure steps multiply along the orbit.

Region by region (`P = pairOrbPerm`): the staircase `T - u ↦ T - u - r` with `w = -1`
(`u = u + r - r`), into the window `σ = -1`; the bottom of the staircase `2c - s ↦ c - s + 1`
(`s - 1 = r - 1 - r + s`); runs and window feet `w = 0`; the low strands
`ℓ(i) + s = ℓ(next) + r w` by `s + i = r ((s + i) / r) + (s + i) % r` (`Nat.div_add_mod`), and
`(r - 1 + s) % r ≠ r - 1` (coprimality) for `2c`. Checked by `pairOrbCheckLab`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The power of `K` of a low strand through the labels of its ends (as `pairOrb_slotW_mul` of
`AJHandoff.TorusKnot.PairKOrbSumVal`). -/
private theorem slotW_mul_lab {r s : ℕ} (h : IsTorusPair r s) (i : ℕ) :
    (r : ℤ) * pairOrbSlotW r s i =
      (if i + 1 = r then 0 else (i : ℤ) + 1) + s -
        (if pairOrbNext r s i + 1 = r then 0 else (pairOrbNext r s i : ℤ) + 1) := by
  obtain ⟨hr, hrs, hcop⟩ := h
  have hd := Nat.div_add_mod (s + i) r
  unfold pairOrbSlotW pairOrbNext
  by_cases hir : i + 1 = r
  · have hj : (s + i) % r + 1 ≠ r := by
      intro hj
      have hdvd : r ∣ s := ⟨(s + i) / r, by
        generalize r * ((s + i) / r) = X at hd ⊢
        omega⟩
      have := Nat.Coprime.eq_one_of_dvd hcop hdvd
      omega
    rw [ite_eq_left hir, ite_eq_left hir, ite_eq_right hj, show r - 1 + s = s + i by omega]
    have hd' : (r : ℤ) * ((s + i) / r : ℕ) + ((s + i) % r : ℕ) = s + i := by exact_mod_cast hd
    have hi' : (i : ℤ) + 1 = r := by exact_mod_cast hir
    linear_combination hd' + hi'
  · have hd' : (r : ℤ) * ((s + i) / r : ℕ) + ((s + i) % r : ℕ) = s + i := by exact_mod_cast hd
    rw [ite_eq_right hir, ite_eq_right hir]
    by_cases hj : (s + i) % r + 1 = r
    · rw [ite_eq_left hj, ite_eq_left hj]
      have hj' : (((s + i) % r : ℕ) : ℤ) + 1 = r := by exact_mod_cast hj
      linear_combination hd' - hj'
    · rw [ite_eq_right hj, ite_eq_right hj]
      linear_combination hd'

/-- The label congruence from the values of the labels and of `w`. -/
private theorem lab_step_of_values {r s t a b : ℕ} {w σ : ℤ} (h1 : pairOrbLab r s t = a)
    (h2 : pairOrbLab r s (pairOrbPerm r s t) = b) (h3 : pairOrbW r s t = w)
    (he : (a : ℤ) = b + r * w + s * σ) :
    ∃ σ : ℤ, (pairOrbLab r s t : ℤ) =
      pairOrbLab r s (pairOrbPerm r s t) + r * pairOrbW r s t + s * σ :=
  ⟨σ, by rw [h1, h2, h3]; exact he⟩

/-- The label congruence on the low strands. -/
private theorem lab_step_low {r s t : ℕ} (h : IsTorusPair r s)
    (ht : t + 2 ≤ r ∨ t = 2 * pairC r s) :
    ∃ σ : ℤ, (pairOrbLab r s t : ℤ) =
      pairOrbLab r s (pairOrbPerm r s t) + r * pairOrbW r s t + s * σ := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  have hcs : pairC r s - s = (r - 2) * s := by
    unfold pairC
    rw [show r - 1 = r - 2 + 1 by omega, Nat.add_mul, one_mul, Nat.add_sub_cancel]
  have hcs' : r = 2 ∧ pairC r s - s = 0 ∨ s ≤ pairC r s - s := by
    rcases Nat.eq_zero_or_pos (r - 2) with h0 | h0
    · left
      rw [hcs, h0, zero_mul]
      omega
    · right
      rw [hcs]
      exact Nat.le_mul_of_pos_left s h0
  have hi : pairOrbLow r s t < r := by
    unfold pairOrbLow
    split_ifs <;> omega
  have hj : pairOrbNext r s (pairOrbLow r s t) < r := Nat.mod_lt _ (by omega)
  have hW : pairOrbW r s t = pairOrbSlotW r s (pairOrbLow r s t) := by
    unfold pairOrbW
    rw [ite_eq_left ht]
  have hL1 : pairOrbLab r s t = if pairOrbLow r s t + 1 = r then 0 else pairOrbLow r s t + 1 := by
    unfold pairOrbLab pairOrbLow pairTop
    split_ifs <;> omega
  have hP : pairOrbLab r s (pairOrbPerm r s t) =
      if pairOrbNext r s (pairOrbLow r s t) + 1 = r then 0
      else pairOrbNext r s (pairOrbLow r s t) + 1 := by
    unfold pairOrbPerm
    rw [ite_eq_left ht]
    unfold pairTop
    split_ifs <;> (unfold pairOrbLab pairTop; split_ifs <;> omega)
  refine ⟨-1, ?_⟩
  rw [hL1, hP, hW, slotW_mul_lab h]
  push_cast
  ring

/-- The label congruence off `pairOrbH1`. -/
theorem pairOrbLab_step {r s : ℕ} (h : IsTorusPair r s) {t : ℕ} (ht : t < pairStrands r s)
    (hH : t ≠ pairOrbH1 r s) :
    ∃ σ : ℤ, (pairOrbLab r s t : ℤ) =
      pairOrbLab r s (pairOrbPerm r s t) + r * pairOrbW r s t + s * σ := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  have hE1 : 1 ≤ pairRunDown r s := by unfold pairRunDown; omega
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hH1 : pairOrbH1 r s = 2 * pairC r s - s - 1 := rfl
  have hm : pairStrands r s = 2 * pairC r s + 1 := rfl
  rw [hH1] at hH
  rw [hm] at ht
  by_cases hlow : t + 2 ≤ r ∨ t = 2 * pairC r s
  · exact lab_step_low h hlow
  have hW0 : t + s + 1 ≤ 2 * pairC r s → pairOrbW r s t = 0 := fun h' ↦ by
    unfold pairOrbW
    rw [ite_eq_right hlow, ite_eq_left h']
  have hW1 : 2 * pairC r s < t + s + 1 → pairOrbW r s t = -1 := fun h' ↦ by
    unfold pairOrbW
    split_ifs <;> omega
  by_cases h3 : t + s + r ≤ 2 * pairC r s
  · refine lab_step_of_values (a := r - 1) (b := r - 1) (σ := 0) ?_ ?_ (hW0 (by omega)) ?_
    · unfold pairOrbLab
      split_ifs <;> omega
    · unfold pairOrbPerm
      split_ifs <;> first | omega | (unfold pairOrbLab; split_ifs <;> omega)
    · ring
  by_cases h5 : t + s + 2 ≤ 2 * pairC r s
  · refine lab_step_of_values (a := 2 * pairC r s - s - 1 - t) (b := 2 * pairC r s - s - 1 - t)
      (σ := 0) ?_ ?_ (hW0 (by omega)) ?_
    · unfold pairOrbLab
      split_ifs <;> omega
    · unfold pairOrbPerm
      split_ifs <;> first | omega | (unfold pairOrbLab; split_ifs <;> omega)
    · ring
  by_cases h6 : t + s = 2 * pairC r s
  · refine lab_step_of_values (a := s - 1) (b := r - 1) (σ := 1) ?_ ?_ (hW1 (by omega)) ?_
    · unfold pairOrbLab
      split_ifs <;> omega
    · unfold pairOrbPerm
      split_ifs <;> first | omega | (unfold pairOrbLab; split_ifs <;> omega)
    · push_cast [Nat.cast_sub (show 1 ≤ s by omega), Nat.cast_sub (show 1 ≤ r by omega)]
      ring
  by_cases h7 : t + 1 < 2 * pairC r s
  · have hP : pairOrbPerm r s t = t - r := by
      unfold pairOrbPerm
      split_ifs <;> omega
    by_cases h8 : t - r + s + 1 ≤ 2 * pairC r s
    · refine lab_step_of_values (a := 2 * pairC r s - 1 - t)
        (b := 2 * pairC r s - s - 1 - (t - r)) (σ := 1) ?_ ?_ (hW1 (by omega)) ?_
      · unfold pairOrbLab
        split_ifs <;> omega
      · rw [hP]
        unfold pairOrbLab
        split_ifs <;> omega
      · omega
    · refine lab_step_of_values (a := 2 * pairC r s - 1 - t)
        (b := 2 * pairC r s - 1 - (t - r)) (σ := 0) ?_ ?_ (hW1 (by omega)) ?_
      · unfold pairOrbLab
        split_ifs <;> omega
      · rw [hP]
        unfold pairOrbLab
        split_ifs <;> omega
      · omega
  · refine lab_step_of_values (a := 0) (b := r) (σ := 0) ?_ ?_ (hW1 (by omega)) ?_
    · unfold pairOrbLab
      split_ifs <;> omega
    · unfold pairOrbPerm
      split_ifs <;> first | omega | (unfold pairOrbLab; split_ifs <;> omega)
    · ring

/-- The label congruence as a conjugation of rounds. -/
theorem pairOrbY_lab_step {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G} (hL : PairGapRels r s L)
    {t : ℕ} (ht : t < pairStrands r s) (hH : t ≠ pairOrbH1 r s) :
    pairOrbY r s L (pairOrbLab r s t) =
      pairOrbK r s L ^ pairOrbW r s t * pairOrbY r s L (pairOrbLab r s (pairOrbPerm r s t)) *
        pairOrbK r s L ^ (-pairOrbW r s t) := by
  obtain ⟨σ, hσ⟩ := pairOrbLab_step h ht hH
  rw [pairOrbK_zpow_conj h hL, hσ, pairOrbY_add_mul_period]

end AJConjecture
