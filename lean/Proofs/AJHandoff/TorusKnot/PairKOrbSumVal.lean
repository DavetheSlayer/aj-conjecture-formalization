import Mathlib
import AJHandoff.TorusKnot.PairKOrbDefs

/-!
# The sums of the exponents over the two blocks

Over the top block without `pairOrbH1`: `∑ w = -s` (the `s` staircase positions `[2c - s, T]`
have `w = -1`) and `∑ n = rs = c + s` (`1` on the `b₀ + r - 2 - (c - s)` positions of the runs
and the window feet and on the `s - 2` inner staircase positions, `2` at `2c - s` and `T`).
Over the bottom block `[0, c - s] ∪ {2c}`: `∑ w = s` and `∑ n = -rs`; only the `r` low strands
contribute. With `λ(i) = i + 1` (`i ≤ r - 2`), `λ(r - 1) = 0`: `r · w(i) = λ(i) + s - λ(next i)`
(`pairOrb_slotW_mul`), and `i ↦ (s + i) % r` permutes `[0, r)` (`pairOrb_sum_rot`), so
`∑ w = s`; `∑ n = -(∑ w + r) - (c - r) = -(s + c) = -rs`, since exactly one low index has next
index `r - 2`. Checked by `pairOrbCheckSums`.

Route: `Finset.sum_Ioc`-style splitting of the intervals and `split_ifs`/`omega` on the
definitions; `Nat.div_add_mod` for `pairOrb_slotW_mul`; `Equiv.sum_comp` with the bijection
`i ↦ (s + i) % r` of `Fin r` (`Fin.addNat`-free: `Finset.sum_bij`) for `pairOrb_sum_rot`.
-/

namespace AJConjecture

set_option linter.unusedVariables false in
/-- The power of `K` of a low strand through the labels of its ends. -/
theorem pairOrb_slotW_mul {r s : ℕ} (h : IsTorusPair r s) {i : ℕ} (hi : i < r) :
    (r : ℤ) * pairOrbSlotW r s i =
      (if i + 1 = r then 0 else (i : ℤ) + 1) + s -
        (if pairOrbNext r s i + 1 = r then 0 else (pairOrbNext r s i : ℤ) + 1) := by
  obtain ⟨hr, hrs, hcop⟩ := h
  have hd := Nat.div_add_mod (s + i) r
  have hd' : (r : ℤ) * ((s + i) / r : ℕ) + ((s + i) % r : ℕ) = s + i := by exact_mod_cast hd
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
    have hi' : (i : ℤ) + 1 = r := by exact_mod_cast hir
    linear_combination hd' + hi'
  · rw [ite_eq_right hir, ite_eq_right hir]
    by_cases hj : (s + i) % r + 1 = r
    · rw [ite_eq_left hj, ite_eq_left hj]
      have hj' : (((s + i) % r : ℕ) : ℤ) + 1 = r := by exact_mod_cast hj
      linear_combination hd' - hj'
    · rw [ite_eq_right hj, ite_eq_right hj]
      linear_combination hd'

/-- Adding `s` modulo `r` permutes the low indices. -/
theorem pairOrb_sum_rot {r : ℕ} (hr : 0 < r) (s : ℕ) (F : ℕ → ℤ) :
    ∑ i ∈ Finset.range r, F ((s + i) % r) = ∑ i ∈ Finset.range r, F i := by
  have hinj : Set.InjOn (fun i ↦ (s + i) % r) (Finset.range r : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have hm : i ≡ j [MOD r] := Nat.ModEq.add_left_cancel' s hij
    unfold Nat.ModEq at hm
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hm
  have himg : (Finset.range r).image (fun i ↦ (s + i) % r) = Finset.range r := by
    refine Finset.eq_of_subset_of_card_le (fun x hx ↦ ?_) ?_
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (Nat.mod_lt _ hr)
    · rw [Finset.card_image_of_injOn hinj]
  rw [← Finset.sum_image (f := F) hinj, himg]

/-- The top block without `pairOrbH1`. -/
private abbrev pairOrbTopSet (r s : ℕ) : Finset ℕ :=
  (Finset.Icc (pairC r s - s + 1) (pairTop r s)).erase (pairOrbH1 r s)

/-- `c + s = rs`. -/
private theorem pairC_add_self {r s : ℕ} (hr : 1 ≤ r) : pairC r s + s = r * s := by
  unfold pairC
  obtain ⟨a, rfl⟩ : ∃ a, r = a + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.add_mul, one_mul]

/-- The sums over the top block. -/
theorem pairOrb_sum_top_val {r s : ℕ} (h : IsTorusPair r s) :
    ∑ t ∈ (Finset.Icc (pairC r s - s + 1) (pairTop r s)).erase (pairOrbH1 r s), pairOrbW r s t =
        -(s : ℤ) ∧
      ∑ t ∈ (Finset.Icc (pairC r s - s + 1) (pairTop r s)).erase (pairOrbH1 r s), pairOrbN r s t =
        ((r * s : ℕ) : ℤ) := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  have hE1 : 1 ≤ pairRunDown r s := by unfold pairRunDown; omega
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hH : pairOrbH1 r s = 2 * pairC r s - s - 1 := rfl
  have hHmem : pairOrbH1 r s ∈ Finset.Icc (pairC r s - s + 1) (pairTop r s) := by
    rw [Finset.mem_Icc]
    omega
  have hcard : (pairOrbTopSet r s).card = pairC r s + s - 2 := by
    rw [Finset.card_erase_of_mem hHmem, Nat.card_Icc]
    omega
  have hmem : ∀ t ∈ pairOrbTopSet r s, pairC r s - s + 1 ≤ t ∧ t ≤ 2 * pairC r s - 1 ∧
      t ≠ 2 * pairC r s - s - 1 := fun t ht ↦ by
    rw [Finset.mem_erase, Finset.mem_Icc] at ht
    omega
  refine ⟨?_, ?_⟩
  · have hW : ∀ t ∈ pairOrbTopSet r s,
        pairOrbW r s t = if t ∈ Finset.Icc (2 * pairC r s - s) (pairTop r s) then -1 else 0 :=
      fun t ht ↦ by
        have := hmem t ht
        simp only [Finset.mem_Icc]
        unfold pairOrbW
        split_ifs <;> omega
    have hsub : Finset.Icc (2 * pairC r s - s) (pairTop r s) ⊆ pairOrbTopSet r s := by
      intro t ht
      rw [Finset.mem_Icc] at ht
      rw [Finset.mem_erase, Finset.mem_Icc]
      omega
    change ∑ t ∈ pairOrbTopSet r s, pairOrbW r s t = _
    rw [Finset.sum_congr rfl hW, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub,
      Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_neg_one]
    congr 1
    push_cast [show pairTop r s + 1 - (2 * pairC r s - s) = s by omega]
    rfl
  · have hN : ∀ t ∈ pairOrbTopSet r s, pairOrbN r s t =
        1 + (if 2 * pairC r s - s = t then 1 else 0) + (if pairTop r s = t then 1 else 0) :=
      fun t ht ↦ by
        have := hmem t ht
        unfold pairOrbN
        split_ifs <;> omega
    have hm1 : 2 * pairC r s - s ∈ pairOrbTopSet r s := by
      rw [Finset.mem_erase, Finset.mem_Icc]
      omega
    have hm2 : pairTop r s ∈ pairOrbTopSet r s := by
      rw [Finset.mem_erase, Finset.mem_Icc]
      omega
    change ∑ t ∈ pairOrbTopSet r s, pairOrbN r s t = _
    rw [Finset.sum_congr rfl hN, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.sum_ite_eq, ite_eq_left hm1, ite_eq_left hm2, Finset.sum_const,
      hcard, nsmul_eq_mul, mul_one, ← pairC_add_self (s := s) (by omega : 1 ≤ r)]
    push_cast [show 2 ≤ pairC r s + s by omega]
    ring

/-- The bottom sum of a function that is `Y` on the low strands and `0` on the decreasing run. -/
private theorem sum_bot_eq_sum_low {r s : ℕ} (h : IsTorusPair r s) (X Y : ℕ → ℤ)
    (hlow : ∀ t, t + 2 ≤ r → X t = Y t)
    (hmid : ∀ t, r - 1 ≤ t → t ≤ pairC r s - s → X t = 0) (h2c : X (2 * pairC r s) = Y (r - 1)) :
    ∑ t ∈ Finset.range (pairC r s - s + 1), X t + X (2 * pairC r s) =
      ∑ i ∈ Finset.range r, Y i := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  have hE1 : 1 ≤ pairRunDown r s := by unfold pairRunDown; omega
  rw [← Finset.sum_range_add_sum_Ico _ (show r - 1 ≤ pairC r s - s + 1 by omega),
    Finset.sum_eq_zero (s := Finset.Ico _ _) fun t ht ↦ by
      rw [Finset.mem_Ico] at ht
      exact hmid t ht.1 (by omega),
    add_zero, h2c, show r = r - 1 + 1 by omega, Finset.sum_range_succ, Nat.add_sub_cancel]
  congr 1
  exact Finset.sum_congr rfl fun t ht ↦ hlow t (by rw [Finset.mem_range] at ht; omega)

/-- The sum of the powers of `K` of the low strands. -/
private theorem sum_slotW {r s : ℕ} (h : IsTorusPair r s) :
    ∑ i ∈ Finset.range r, pairOrbSlotW r s i = s := by
  have hr : 0 < r := by have := h.1; omega
  have key : (r : ℤ) * ∑ i ∈ Finset.range r, pairOrbSlotW r s i = r * s := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun i hi ↦
      pairOrb_slotW_mul h (Finset.mem_range.1 hi), Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    have hrot := pairOrb_sum_rot hr s (fun j ↦ if j + 1 = r then 0 else (j : ℤ) + 1)
    unfold pairOrbNext
    rw [hrot]
    simp
  exact mul_left_cancel₀ (by exact_mod_cast hr.ne') key

/-- The sums over the bottom block. -/
theorem pairOrb_sum_bot_val {r s : ℕ} (h : IsTorusPair r s) :
    ∑ t ∈ Finset.range (pairC r s - s + 1), pairOrbW r s t + pairOrbW r s (2 * pairC r s) =
        (s : ℤ) ∧
      ∑ t ∈ Finset.range (pairC r s - s + 1), pairOrbN r s t + pairOrbN r s (2 * pairC r s) =
        -((r * s : ℕ) : ℤ) := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  have hlow : ∀ t, t + 2 ≤ r → pairOrbLow r s t = t := fun t ht ↦ by
    unfold pairOrbLow
    rw [ite_eq_right (by omega)]
  have h2c : pairOrbLow r s (2 * pairC r s) = r - 1 := by
    unfold pairOrbLow
    rw [ite_eq_left rfl]
  refine ⟨?_, ?_⟩
  · rw [sum_bot_eq_sum_low h _ (pairOrbSlotW r s), sum_slotW h]
    · intro t ht
      unfold pairOrbW
      rw [ite_eq_left (Or.inl ht), hlow t ht]
    · intro t h1 h2
      unfold pairOrbW
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    · unfold pairOrbW
      rw [ite_eq_left (Or.inr rfl), h2c]
  · rw [sum_bot_eq_sum_low h _ (pairOrbSlotN r s)]
    · unfold pairOrbSlotN
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_add_distrib, sum_slotW h,
        Finset.sum_const, Finset.card_range]
      have hrot := pairOrb_sum_rot (by omega : 0 < r) s
        (fun j ↦ if j + 2 = r then ((pairC r s - r : ℕ) : ℤ) else 0)
      unfold pairOrbNext
      have hcond : ∀ i : ℕ, (i + 2 = r ↔ i = r - 2) := fun i ↦ by omega
      simp only [hcond] at hrot ⊢
      have hmem : r - 2 ∈ Finset.range r := Finset.mem_range.2 (by omega)
      rw [hrot, Finset.sum_ite_eq', ite_eq_left hmem, nsmul_eq_mul, mul_one,
        ← pairC_add_self (s := s) (by omega : 1 ≤ r)]
      push_cast [show r ≤ pairC r s by omega]
      ring
    · intro t ht
      unfold pairOrbN
      rw [ite_eq_left (Or.inl ht), hlow t ht]
    · intro t h1 h2
      unfold pairOrbN
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    · unfold pairOrbN
      rw [ite_eq_left (Or.inr rfl), h2c]

end AJConjecture
