import Mathlib
import AJHandoff.TorusKnot.PairKOrbRounds
import AJHandoff.TorusKnot.PairKOrbSkip

/-!
# Pure forms of the strand loops: the low strands (crux)

For block loops with the gap relations, the loop of the low strand of low index `i`
(`pairOrbSlotLoop`, the position `i ≤ r - 2` or `2c`) is pure in the frame of `y_0`:
`y_0 · S · y_0⁻¹ = K ^ w * y_ρ ^ n` with `j = (s + i) % r`, `ρ = ℓ(P t)` (`j + 1` for
`j ≤ r - 2`, `0` for `j = r - 1`), `w = pairOrbSlotW r s i`, `n = pairOrbSlotN r s i`.

Computation (`D(n) = y_(n-1) ⋯ y_0`, `e = i + 1` for `i ≤ r - 2`, `e = 0` for `2c`):
`y_0 · prefix = D(e)` (`pairOrb_climbs`: the `D'`-prefix is `y_0⁻¹ (y_i ⋯ y_1) y_0`, and
`C = y_0⁻¹`); the rounds of `pairOrbSkip` are `y_u` (`pairOrbY_natCast`); the tail times `y_0⁻¹`
is `D(ρ + 1)⁻¹` for `j ≤ r - 3`, `y_0⁻¹ = D(1)⁻¹` for `j = r - 1`, and
`y_(-1)^(-(z+2)) D(r - 1)⁻¹ = D(r)⁻¹ y_(r-1)^(-(z+1))` for `j = r - 2` (`pairOrb_runs`, window
relation). Then `pairOrb_skip_frame` with `s + e = ρ + r w` gives
`D(e) · skip · D(ρ)⁻¹ = K ^ w y_ρ^(-w)`, and `D(ρ + 1)⁻¹ = D(ρ)⁻¹ y_ρ⁻¹` gives the extra `y_ρ⁻¹`.
Checked exactly in the torus knot group (`AJHandoff.TorusKnot.PairKOrbDefs`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-! ### Descending products and the window -/

/-- Splitting off the top factor of a descending product. -/
private theorem descProd_succ_top_plow (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = g (a + n) * descProd g a n := by
  simp [descProd, List.range_succ]

/-- Splitting off the bottom factor of a descending product. -/
private theorem descProd_succ_bot_plow (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = descProd g (a + 1) n * g a := by
  induction n with
  | zero => simp [descProd]
  | succ n ih =>
    rw [descProd_succ_top_plow, ih, descProd_succ_top_plow, mul_assoc,
      show a + 1 + n = a + (n + 1) by omega]

/-- A descending product of a constant factor is a power. -/
private theorem descProd_const_plow (g : ℕ → G) (a n : ℕ) (x : G)
    (H : ∀ i, i < n → g (a + i) = x) : descProd g a n = x ^ n := by
  induction n with
  | zero => simp [descProd]
  | succ n ih =>
    rw [descProd_succ_top_plow, H n (by omega), ih fun i hi ↦ H i (by omega), pow_succ']

/-- Descending products with the same factors agree. -/
private theorem descProd_congr_plow (g g' : ℕ → G) (a b n : ℕ)
    (H : ∀ i, i < n → g (a + i) = g' (b + i)) : descProd g a n = descProd g' b n := by
  induction n with
  | zero => simp [descProd]
  | succ n ih =>
    rw [descProd_succ_top_plow, descProd_succ_top_plow, H n (by omega),
      ih fun i hi ↦ H i (by omega)]

/-- A descending product from `0` of length `n + 2`, top and bottom factors split off. -/
private theorem descProd_two_plow (g : ℕ → G) (n : ℕ) :
    descProd g 0 (n + 2) = g (n + 1) * descProd g 1 n * g 0 := by
  rw [descProd_succ_top_plow, descProd_succ_bot_plow, zero_add, mul_assoc]

/-- A descending product from `0` of length `n + 2`, two bottom factors split off. -/
private theorem descProd_two_bot_plow (g : ℕ → G) (n : ℕ) :
    descProd g 0 (n + 2) = descProd g 2 n * g 1 * g 0 := by
  rw [descProd_succ_bot_plow, descProd_succ_bot_plow]

/-- The two windows `y_(r-1) ⋯ y_0` and `y_(r-2) ⋯ y_0 y_(-1)` give `K`. -/
private theorem pairOrbK_windows_plow {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) :
    pairOrbK r s L = pairOrbY r s L ((r - 1 : ℕ) : ℤ) *
        descProd (fun k ↦ pairOrbY r s L k) 1 (r - 2) * pairOrbY r s L 0 ∧
      pairOrbK r s L = descProd (fun k ↦ pairOrbY r s L k) 1 (r - 2) * pairOrbY r s L 0 *
        pairOrbY r s L (-1) := by
  have hr : 2 ≤ r := h.1
  refine ⟨?_, ?_⟩
  · have e := descProd_two_plow (fun k : ℕ ↦ pairOrbY r s L ((0 : ℤ) + k)) (r - 2)
    rw [show r - 2 + 2 = r by omega, pairOrb_window h hL 0, show r - 2 + 1 = r - 1 by omega] at e
    rw [e]
    simp only [zero_add, Nat.cast_zero]
  · have e := descProd_two_bot_plow (fun k : ℕ ↦ pairOrbY r s L ((-1 : ℤ) + k)) (r - 2)
    rw [show r - 2 + 2 = r by omega, pairOrb_window h hL (-1)] at e
    rw [e]
    congr 1
    · congr 1
      · refine descProd_congr_plow _ _ _ _ _ fun i _ ↦ ?_
        congr 1
        push_cast
        ring

/-- The window relation `y_(r-1) = D y_(-1) D⁻¹` with `D = y_(r-2) ⋯ y_0`. -/
private theorem pairOrbY_window_plow {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) :
    pairOrbY r s L ((r - 1 : ℕ) : ℤ) =
      descProd (fun k ↦ pairOrbY r s L k) 1 (r - 2) * pairOrbY r s L 0 * pairOrbY r s L (-1) *
        (descProd (fun k ↦ pairOrbY r s L k) 1 (r - 2) * pairOrbY r s L 0)⁻¹ := by
  obtain ⟨h0, h1⟩ := pairOrbK_windows_plow h hL
  rw [← h1, h0]
  group

/-! ### The three parts of a low loop -/

/-- The prefix of a low loop in the frame of `y_0`: `y_0 · prefix = y_(e-1) ⋯ y_0`. -/
private theorem pureLow_prefix {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) {i : ℕ} (hi : i < r) :
    pairOrbY r s L 0 * (if i + 1 = r then L (pairIdxC r s)
      else descProd (fun j ↦ L (pairIdxDp r s j)) (r - 2 - i) i) =
      descProd (fun k ↦ pairOrbY r s L k) 0 (if i + 1 = r then 0 else i + 1) := by
  obtain ⟨hC, -, hD⟩ := pairOrb_climbs h hL
  split_ifs with hir
  · rw [hC, mul_inv_cancel]
    simp [descProd]
  · rw [hD i (by omega), descProd_succ_bot_plow]
    group

/-- The rounds collected by a low loop, as rounds `y_u`. -/
private theorem pureLow_skip {r s : ℕ} (L : ℕ → G) {a ρ : ℕ} (hρ : a % r = ρ % r) :
    pairOrbSkip r s L a =
      ((List.range s).reverse.map fun u ↦ if u % r = ρ % r then 1 else pairOrbY r s L u).prod := by
  unfold pairOrbSkip
  congr 1
  refine List.map_congr_left fun u hu ↦ ?_
  rw [List.mem_reverse, List.mem_range] at hu
  rw [hρ, pairOrbY_natCast L hu]

/-- The tail of a low loop in the frame of `y_0`. -/
private theorem pureLow_suffix {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) {j : ℕ} (hj : j < r) :
    pairOrbSuf r s L j * (pairOrbY r s L 0)⁻¹ =
      (descProd (fun k ↦ pairOrbY r s L k) 0 (if j + 1 = r then 0 else j + 1))⁻¹ *
        pairOrbY r s L ((if j + 1 = r then 0 else j + 1 : ℕ) : ℤ) ^
          (-(1 + if j + 2 = r then ((pairC r s - r : ℕ) : ℤ) else 0)) := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  have hE1 : 1 ≤ pairRunDown r s := by unfold pairRunDown; omega
  have hz : pairRunUp r s = pairC r s - r - 1 := rfl
  obtain ⟨-, hA, -⟩ := pairOrb_climbs h hL
  obtain ⟨hB, hRun⟩ := pairOrb_runs h hL
  unfold pairOrbSuf
  by_cases h3 : j + 3 ≤ r
  · rw [ite_eq_left h3, ite_eq_right (show ¬ j + 1 = r by omega),
      ite_eq_right (show ¬ j + 2 = r by omega), hA (j + 1) (by omega),
      descProd_succ_top_plow, descProd_succ_bot_plow, add_comm 1 j]
    simp only [zero_add, add_zero]
    group
  by_cases h2 : j + 2 = r
  · rw [ite_eq_right h3, ite_eq_left h2, ite_eq_right (show ¬ j + 1 = r by omega),
      ite_eq_left h2, hB, hA (r - 2) le_rfl]
    have hrun : descProd L (r - 2 + pairRunDown r s) (pairRunUp r s) =
        (pairOrbY r s L (-1))⁻¹ ^ pairRunUp r s := by
      refine descProd_const_plow _ _ _ _ fun i hi ↦ ?_
      have e := hRun (r - 2 + pairRunDown r s + i + 1) (by omega) (by omega)
      rwa [show pairIdxRun r s (r - 2 + pairRunDown r s + i + 1) =
        r - 2 + pairRunDown r s + i by unfold pairIdxRun; split_ifs <;> omega] at e
    have hlow : L (r - 2) = (pairOrbY r s L (-1))⁻¹ := by
      have e := hRun (r + pairRunDown r s - 2) (by omega) (by omega)
      rwa [show pairIdxRun r s (r + pairRunDown r s - 2) = r - 2 by
        unfold pairIdxRun; split_ifs <;> omega] at e
    have hcr : pairC r s - r = pairRunUp r s + 1 := by omega
    rw [hrun, hlow, show j + 1 = r - 1 by omega, pairOrbY_window_plow h hL, conj_zpow,
      show r - 1 = r - 2 + 1 by omega, descProd_succ_bot_plow, hcr]
    simp only [zero_add, Nat.cast_add, Nat.cast_one]
    rw [← zpow_natCast]
    group
  · have h1 : j + 1 = r := by omega
    rw [ite_eq_right h3, ite_eq_right h2, ite_eq_left h1, ite_eq_right h2]
    simp [descProd]

/-! ### The exponent of `K` -/

/-- The frame condition `s + e = ρ + r w` of a low strand. -/
private theorem pureLow_frame {r s : ℕ} (h : IsTorusPair r s) (i : ℕ) :
    ∃ w : ℕ, s + (if i + 1 = r then 0 else i + 1) =
        (if pairOrbNext r s i + 1 = r then 0 else pairOrbNext r s i + 1) + r * w ∧
      (w : ℤ) = pairOrbSlotW r s i := by
  obtain ⟨hr, hrs, hcop⟩ := h
  unfold pairOrbSlotW pairOrbNext
  by_cases hir : i + 1 = r
  · have hd := Nat.div_add_mod (s + i) r
    have hj : (s + i) % r + 1 ≠ r := by
      intro hj
      have hdvd : r ∣ s := ⟨(s + i) / r, by
        generalize r * ((s + i) / r) = X at hd ⊢
        omega⟩
      have := Nat.Coprime.eq_one_of_dvd hcop hdvd
      omega
    have hq : 1 ≤ (s + i) / r := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      omega
    refine ⟨(s + i) / r - 1, ?_, ?_⟩
    · rw [ite_eq_left hir, ite_eq_right hj, Nat.mul_sub, mul_one]
      have := Nat.mul_le_mul_left r hq
      rw [mul_one] at this
      omega
    · rw [ite_eq_left hir, show r - 1 + s = s + i by omega]
      push_cast [hq]
      ring
  · have hd := Nat.div_add_mod (s + i) r
    by_cases hj : (s + i) % r + 1 = r
    · refine ⟨(s + i) / r + 1, ?_, ?_⟩
      · rw [ite_eq_right hir, ite_eq_left hj, Nat.mul_add, mul_one]
        omega
      · rw [ite_eq_right hir, ite_eq_left hj]
        push_cast
        ring
    · refine ⟨(s + i) / r, ?_, ?_⟩
      · rw [ite_eq_right hir, ite_eq_right hj]
        omega
      · rw [ite_eq_right hir, ite_eq_right hj]
        simp

/-! ### The low loops -/

/-- The loop of the low strand of low index `i` is pure. -/
private theorem pureLow_slot {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) {i : ℕ} (hi : i < r) :
    pairOrbConj r s L (pairOrbSlotLoop r s L i) =
      pairOrbK r s L ^ pairOrbSlotW r s i *
        pairOrbY r s L ((if pairOrbNext r s i + 1 = r then 0 else pairOrbNext r s i + 1 : ℕ) :
          ℤ) ^ pairOrbSlotN r s i := by
  have hr : 2 ≤ r := h.1
  have hj : pairOrbNext r s i < r := Nat.mod_lt _ (by omega)
  obtain ⟨w, hw, hwW⟩ := pureLow_frame h i
  set ρ := if pairOrbNext r s i + 1 = r then 0 else pairOrbNext r s i + 1 with hρdef
  have hρ : ρ < r := by rw [hρdef]; split_ifs <;> omega
  have hmod : (pairOrbNext r s i + 1) % r = ρ % r := by
    rw [hρdef]
    split_ifs with h1
    · rw [h1, Nat.mod_self, Nat.zero_mod]
    · rfl
  have hframe := pairOrb_skip_frame (by omega : 1 ≤ r) (pairOrbK r s L) (pairOrbY r s L)
    (pairOrb_window h hL) (pairOrbY_add_period r s L)
    (show (if i + 1 = r then 0 else i + 1) < r by split_ifs <;> omega) hρ hw
  have hsplit : pairOrbConj r s L (pairOrbSlotLoop r s L i) =
      (pairOrbY r s L 0 * (if i + 1 = r then L (pairIdxC r s)
        else descProd (fun j ↦ L (pairIdxDp r s j)) (r - 2 - i) i)) *
        pairOrbSkip r s L (pairOrbNext r s i + 1) *
        (pairOrbSuf r s L (pairOrbNext r s i) * (pairOrbY r s L 0)⁻¹) := by
    unfold pairOrbConj pairOrbSlotLoop
    group
  rw [hsplit, pureLow_prefix h hL hi, pureLow_skip L hmod, pureLow_suffix h hL hj, ← hρdef,
    ← mul_assoc, hframe]
  unfold pairOrbSlotN
  rw [← hwW, zpow_natCast, mul_assoc, ← zpow_add]
  congr 2
  ring

/-- The loops of the low strands are pure. -/
theorem pairOrb_pure_low {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G} (hL : PairGapRels r s L)
    {t : ℕ} (ht : t + 2 ≤ r ∨ t = 2 * pairC r s) :
    pairOrbConj r s L (pairOrbCore r s L t) =
      pairOrbK r s L ^ pairOrbW r s t *
        pairOrbY r s L (pairOrbLab r s (pairOrbPerm r s t)) ^ pairOrbN r s t := by
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
  have hc : pairOrbCore r s L t = pairOrbSlotLoop r s L (pairOrbLow r s t) := by
    unfold pairOrbCore
    rw [ite_eq_left ht]
  have hW : pairOrbW r s t = pairOrbSlotW r s (pairOrbLow r s t) := by
    unfold pairOrbW
    rw [ite_eq_left ht]
  have hN : pairOrbN r s t = pairOrbSlotN r s (pairOrbLow r s t) := by
    unfold pairOrbN
    rw [ite_eq_left ht]
  have hP : pairOrbLab r s (pairOrbPerm r s t) =
      if pairOrbNext r s (pairOrbLow r s t) + 1 = r then 0
      else pairOrbNext r s (pairOrbLow r s t) + 1 := by
    unfold pairOrbPerm
    rw [ite_eq_left ht]
    unfold pairTop
    split_ifs <;> (unfold pairOrbLab pairTop; split_ifs <;> omega)
  rw [hc, hW, hN, hP]
  exact pureLow_slot h hL hi

end AJConjecture
