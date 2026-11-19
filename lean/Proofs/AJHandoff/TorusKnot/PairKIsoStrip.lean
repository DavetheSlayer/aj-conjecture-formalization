import Mathlib
import AJHandoff.TorusKnot.PairKIsoStripAttach

/-!
# Phase I for `Wh⁻₀(T(r, s))`

`isoFenceWord_pairBlocks`: for `r ≥ 3` the fence word of `pairBlocks r s` is `pairStrip r s`
(evaluation of the generic definitions block by block: which discs a block opens and closes and
how many discs of smaller index are open; by regimes, with `List.flatMap` over the runs).
`morseReach_pair_source_strip`: the source word of Theorem T reaches the strip word.
-/

namespace AJConjecture

/-- The arithmetic of an admissible pair with `r ≥ 3`. -/
private theorem pairStrip_arith {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    r + 1 ≤ s ∧ 2 * s ≤ pairC r s ∧ pairRunDown r s + s + r = pairC r s + 3 ∧
      s ≤ pairRunDown r s := by
  obtain ⟨-, hrs, -, hE⟩ := pairBlocks_arith_iso h
  refine ⟨hrs, ?_, hE, ?_⟩
  · simp only [pairC]
    have : 2 ≤ r - 1 := by omega
    nlinarith
  · simp only [pairRunDown]
    have : 1 ≤ r - 2 := by omega
    have : s - 1 ≤ (r - 2) * (s - 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- The index of the first block attached to the disc `m` of `pairBlocks r s`, in terms of
`r`, `E`, `z`, `T`. -/
private def fstZ (r E z T m : ℤ) : ℤ :=
  if m ≤ r - 3 then m
  else if m = r - 2 then r - 3 + E
  else if m ≤ r + E - 3 then 2 * r + E - 5 - m
  else if m = r + E - 2 then r - 2
  else if m ≤ r + E - 2 + z then m - 1
  else if m < T - r then r + E + z + 1 + (T - r - 1 - m)
  else if m = T - r then r - 1 + E + z
  else if m = T + 1 - r then r - 2 + E + z
  else if m < T then T - 1 - m
  else if m = T then r - 1 + E + z
  else r + E + z

/-- The cases of `fstZ`. -/
private theorem fstZ_spec (r E z T m : ℤ) :
    (m ≤ r - 3 ∧ fstZ r E z T m = m) ∨
    (m = r - 2 ∧ fstZ r E z T m = r - 3 + E) ∨
    (r - 2 < m ∧ m ≤ r + E - 3 ∧ fstZ r E z T m = 2 * r + E - 5 - m) ∨
    (r - 2 < m ∧ r + E - 3 < m ∧ m = r + E - 2 ∧ fstZ r E z T m = r - 2) ∨
    (r - 2 < m ∧ r + E - 2 < m ∧ m ≤ r + E - 2 + z ∧ fstZ r E z T m = m - 1) ∨
    (r - 2 < m ∧ r + E - 2 < m ∧ r + E - 2 + z < m ∧ m < T - r ∧
      fstZ r E z T m = r + E + z + 1 + (T - r - 1 - m)) ∨
    (r - 2 < m ∧ r + E - 2 < m ∧ r + E - 2 + z < m ∧ m = T - r ∧ fstZ r E z T m = r - 1 + E + z) ∨
    (r - 2 < m ∧ r + E - 2 < m ∧ r + E - 2 + z < m ∧ T - r < m ∧ m = T + 1 - r ∧
      fstZ r E z T m = r - 2 + E + z) ∨
    (r - 2 < m ∧ r + E - 2 < m ∧ r + E - 2 + z < m ∧ T + 1 - r < m ∧ m < T ∧
      fstZ r E z T m = T - 1 - m) ∨
    (r - 2 < m ∧ r + E - 2 < m ∧ r + E - 2 + z < m ∧ T + 1 - r < m ∧ m = T ∧
      fstZ r E z T m = r - 1 + E + z) ∨
    (r - 2 < m ∧ r + E - 2 < m ∧ r + E - 2 + z < m ∧ T + 1 - r < m ∧ T < m ∧
      fstZ r E z T m = r + E + z) := by
  unfold fstZ
  by_cases h1 : m ≤ r - 3
  · exact Or.inl ⟨h1, ite_eq_left h1⟩
  rw [ite_eq_right h1]
  refine Or.inr ?_
  by_cases h2 : m = r - 2
  · exact Or.inl ⟨h2, ite_eq_left h2⟩
  rw [ite_eq_right h2]
  refine Or.inr ?_
  by_cases h3 : m ≤ r + E - 3
  · exact Or.inl ⟨by omega, h3, ite_eq_left h3⟩
  rw [ite_eq_right h3]
  refine Or.inr ?_
  by_cases h4 : m = r + E - 2
  · exact Or.inl ⟨by omega, by omega, h4, ite_eq_left h4⟩
  rw [ite_eq_right h4]
  refine Or.inr ?_
  by_cases h5 : m ≤ r + E - 2 + z
  · exact Or.inl ⟨by omega, by omega, h5, ite_eq_left h5⟩
  rw [ite_eq_right h5]
  refine Or.inr ?_
  by_cases h6 : m < T - r
  · exact Or.inl ⟨by omega, by omega, by omega, h6, ite_eq_left h6⟩
  rw [ite_eq_right h6]
  refine Or.inr ?_
  by_cases h7 : m = T - r
  · exact Or.inl ⟨by omega, by omega, by omega, h7, ite_eq_left h7⟩
  rw [ite_eq_right h7]
  refine Or.inr ?_
  by_cases h8 : m = T + 1 - r
  · exact Or.inl ⟨by omega, by omega, by omega, by omega, h8, ite_eq_left h8⟩
  rw [ite_eq_right h8]
  refine Or.inr ?_
  by_cases h9 : m < T
  · exact Or.inl ⟨by omega, by omega, by omega, by omega, h9, ite_eq_left h9⟩
  rw [ite_eq_right h9]
  refine Or.inr ?_
  by_cases h10 : m = T
  · exact Or.inl ⟨by omega, by omega, by omega, by omega, h10, ite_eq_left h10⟩
  rw [ite_eq_right h10]
  refine Or.inr ?_
  exact ⟨by omega, by omega, by omega, by omega, by omega, rfl⟩

/-- The index of the last block attached to the disc `m` of `pairBlocks r s`. -/
private def lstZ (r s E z T m : ℤ) : ℤ :=
  if m ≤ r - 3 then r + E + z + 1 + s + (r - 3 - m)
  else if m = r - 2 then r + E + z + 1 + s - 2
  else if m ≤ r + E - 3 then 2 * r + E - 4 - m
  else if m ≤ r + E - 2 + z then m
  else if m < T - s then r + E + z + 1 + s + (m - (T + 2 - s - r))
  else if m = T - s then r + E + z + 1 + s - 1
  else if m = T + 1 - s then r + E + z + 1 + s - 2
  else if m < T then r + E + z + 1 + (T - 1 - m)
  else r + E + z + 1 + s + r - 2

/-- The cases of `lstZ`. -/
private theorem lstZ_spec (r s E z T m : ℤ) :
    (m ≤ r - 3 ∧ lstZ r s E z T m = r + E + z + 1 + s + (r - 3 - m)) ∨
    (m = r - 2 ∧ lstZ r s E z T m = r + E + z + 1 + s - 2) ∨
    (r - 2 < m ∧ m ≤ r + E - 3 ∧ lstZ r s E z T m = 2 * r + E - 4 - m) ∨
    (r - 2 < m ∧ r + E - 3 < m ∧ m ≤ r + E - 2 + z ∧ lstZ r s E z T m = m) ∨
    (r - 2 < m ∧ r + E - 3 < m ∧ r + E - 2 + z < m ∧ m < T - s ∧
      lstZ r s E z T m = r + E + z + 1 + s + (m - (T + 2 - s - r))) ∨
    (r - 2 < m ∧ r + E - 3 < m ∧ r + E - 2 + z < m ∧ m = T - s ∧
      lstZ r s E z T m = r + E + z + 1 + s - 1) ∨
    (r - 2 < m ∧ r + E - 3 < m ∧ r + E - 2 + z < m ∧ T - s < m ∧ m = T + 1 - s ∧
      lstZ r s E z T m = r + E + z + 1 + s - 2) ∨
    (r - 2 < m ∧ r + E - 3 < m ∧ r + E - 2 + z < m ∧ T + 1 - s < m ∧ m < T ∧
      lstZ r s E z T m = r + E + z + 1 + (T - 1 - m)) ∨
    (r - 2 < m ∧ r + E - 3 < m ∧ r + E - 2 + z < m ∧ T + 1 - s < m ∧ T ≤ m ∧
      lstZ r s E z T m = r + E + z + 1 + s + r - 2) := by
  unfold lstZ
  by_cases h1 : m ≤ r - 3
  · exact Or.inl ⟨h1, ite_eq_left h1⟩
  rw [ite_eq_right h1]
  refine Or.inr ?_
  by_cases h2 : m = r - 2
  · exact Or.inl ⟨h2, ite_eq_left h2⟩
  rw [ite_eq_right h2]
  refine Or.inr ?_
  by_cases h3 : m ≤ r + E - 3
  · exact Or.inl ⟨by omega, h3, ite_eq_left h3⟩
  rw [ite_eq_right h3]
  refine Or.inr ?_
  by_cases h4 : m ≤ r + E - 2 + z
  · exact Or.inl ⟨by omega, by omega, h4, ite_eq_left h4⟩
  rw [ite_eq_right h4]
  refine Or.inr ?_
  by_cases h5 : m < T - s
  · exact Or.inl ⟨by omega, by omega, by omega, h5, ite_eq_left h5⟩
  rw [ite_eq_right h5]
  refine Or.inr ?_
  by_cases h6 : m = T - s
  · exact Or.inl ⟨by omega, by omega, by omega, h6, ite_eq_left h6⟩
  rw [ite_eq_right h6]
  refine Or.inr ?_
  by_cases h7 : m = T + 1 - s
  · exact Or.inl ⟨by omega, by omega, by omega, by omega, h7, ite_eq_left h7⟩
  rw [ite_eq_right h7]
  refine Or.inr ?_
  by_cases h8 : m < T
  · exact Or.inl ⟨by omega, by omega, by omega, by omega, h8, ite_eq_left h8⟩
  rw [ite_eq_right h8]
  refine Or.inr ?_
  exact ⟨by omega, by omega, by omega, by omega, by omega, rfl⟩

/-- The first block of the disc `m` of `pairBlocks r s`. -/
private def pairFirst (r s m : ℕ) : ℤ := fstZ r (pairRunDown r s) (pairRunUp r s) (pairTop r s) m

/-- The last block of the disc `m` of `pairBlocks r s`. -/
private def pairLast (r s m : ℕ) : ℤ := lstZ r s (pairRunDown r s) (pairRunUp r s) (pairTop r s) m

/-- The additive arithmetic of an admissible pair with `r ≥ 3`. -/
private theorem pairStrip_ctx {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    r + 1 ≤ s ∧ 2 * s ≤ pairC r s ∧ pairRunDown r s + s + r = pairC r s + 3 ∧
      s ≤ pairRunDown r s ∧ pairTop r s + 1 = 2 * pairC r s ∧
      pairRunUp r s + r + 1 = pairC r s := by
  obtain ⟨h1, h2, h3, h4⟩ := pairStrip_arith h hr
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · simp only [pairTop]
    omega
  · simp only [pairRunUp]
    omega

/-- The discs of the left climb are first and last attached around it. -/
private theorem pairStrip_bound_climb {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {m j : ℕ}
    (hj : j < r - 2)
    (ha : j = m ∨ pairTop r s - 1 - j = m) :
    pairFirst r s m ≤ ((j : ℕ) : ℤ) ∧ ((j : ℕ) : ℤ) ≤ pairLast r s m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pairStrip_ctx h hr
  clear h
  have hf := fstZ_spec r (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  have hl := lstZ_spec r s (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  simp only [pairFirst, pairLast]
  omega

/-- The discs of the block of the decreasing run are first and last attached around it. -/
private theorem pairStrip_bound_runDown {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {m j : ℕ}
    (hj : j < pairRunDown r s)
    (ha : r + pairRunDown r s - 3 - j = m ∨ r + pairRunDown r s - 2 - j = m) :
    pairFirst r s m ≤ ((r - 2 + j : ℕ) : ℤ) ∧ ((r - 2 + j : ℕ) : ℤ) ≤ pairLast r s m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pairStrip_ctx h hr
  clear h
  have hf := fstZ_spec r (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  have hl := lstZ_spec r s (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  simp only [pairFirst, pairLast]
  omega

/-- The discs of the block of the increasing run are first and last attached around it. -/
private theorem pairStrip_bound_runUp {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {m j : ℕ}
    (hj : j < pairRunUp r s)
    (ha : r - 2 + pairRunDown r s + j = m ∨ r - 1 + pairRunDown r s + j = m) :
    pairFirst r s m ≤ ((r - 2 + pairRunDown r s + j : ℕ) : ℤ) ∧
        ((r - 2 + pairRunDown r s + j : ℕ) : ℤ) ≤ pairLast r s m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pairStrip_ctx h hr
  clear h
  have hf := fstZ_spec r (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  have hl := lstZ_spec r s (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  simp only [pairFirst, pairLast]
  omega

/-- The discs of the big climb are first and last attached around it. -/
private theorem pairStrip_bound_bigClimb {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {m : ℕ}
    (ha : r - 2 + pairRunDown r s + pairRunUp r s = m ∨ pairTop r s + 1 - r = m) :
    pairFirst r s m ≤ ((r - 2 + pairRunDown r s + pairRunUp r s : ℕ) : ℤ) ∧
        ((r - 2 + pairRunDown r s + pairRunUp r s : ℕ) : ℤ) ≤ pairLast r s m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pairStrip_ctx h hr
  clear h
  have hf := fstZ_spec r (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  have hl := lstZ_spec r s (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  simp only [pairFirst, pairLast]
  omega

/-- The discs of the round `0` are first and last attached around it. -/
private theorem pairStrip_bound_roundZero {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {m : ℕ}
    (ha : pairTop r s - r = m ∨ pairTop r s = m) :
    pairFirst r s m ≤ ((r - 2 + pairRunDown r s + pairRunUp r s + 1 : ℕ) : ℤ) ∧
        ((r - 2 + pairRunDown r s + pairRunUp r s + 1 : ℕ) : ℤ) ≤ pairLast r s m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pairStrip_ctx h hr
  clear h
  have hf := fstZ_spec r (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  have hl := lstZ_spec r s (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  simp only [pairFirst, pairLast]
  omega

/-- The discs of the first Hopf letter are first and last attached around it. -/
private theorem pairStrip_bound_hopfFirst {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {m : ℕ}
    (ha : pairTop r s = m ∨ pairTop r s + 1 = m) :
    pairFirst r s m ≤ ((r - 2 + pairRunDown r s + pairRunUp r s + 2 : ℕ) : ℤ) ∧
        ((r - 2 + pairRunDown r s + pairRunUp r s + 2 : ℕ) : ℤ) ≤ pairLast r s m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pairStrip_ctx h hr
  clear h
  have hf := fstZ_spec r (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  have hl := lstZ_spec r s (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  simp only [pairFirst, pairLast]
  omega

/-- The discs of the middle round are first and last attached around it. -/
private theorem pairStrip_bound_round {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {m j : ℕ}
    (hj : j < s - 2)
    (ha : pairTop r s - r - 1 - j = m ∨ pairTop r s - 1 - j = m) :
    pairFirst r s m ≤ ((r - 2 + pairRunDown r s + pairRunUp r s + 3 + j : ℕ) : ℤ) ∧
        ((r - 2 + pairRunDown r s + pairRunUp r s + 3 + j : ℕ) : ℤ) ≤ pairLast r s m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pairStrip_ctx h hr
  clear h
  have hf := fstZ_spec r (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  have hl := lstZ_spec r s (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  simp only [pairFirst, pairLast]
  omega

/-- The discs of the last round are first and last attached around it. -/
private theorem pairStrip_bound_lastRound {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {m : ℕ}
    (ha : r - 2 = m ∨ pairTop r s + 1 - s = m) :
    pairFirst r s m ≤ ((r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) : ℕ) : ℤ) ∧
        ((r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) : ℕ) : ℤ) ≤ pairLast r s m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pairStrip_ctx h hr
  clear h
  have hf := fstZ_spec r (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  have hl := lstZ_spec r s (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  simp only [pairFirst, pairLast]
  omega

/-- The discs of the top-right climb are first and last attached around it. -/
private theorem pairStrip_bound_topRight {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {m : ℕ}
    (ha : pairTop r s - s = m ∨ pairTop r s = m) :
    pairFirst r s m ≤ ((r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 1 : ℕ) : ℤ) ∧
        ((r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 1 : ℕ) : ℤ) ≤ pairLast r s m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pairStrip_ctx h hr
  clear h
  have hf := fstZ_spec r (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  have hl := lstZ_spec r s (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  simp only [pairFirst, pairLast]
  omega

/-- The discs of the right descent are first and last attached around it. -/
private theorem pairStrip_bound_descent {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {m j : ℕ}
    (hj : j < r - 2)
    (ha : r - 3 - j = m ∨ pairTop r s + 2 - s - r + j = m) :
    pairFirst r s m ≤ ((r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 + j : ℕ) : ℤ) ∧
        ((r - 2 + pairRunDown r s + pairRunUp r s + 3 +
        (s - 2) + 2 + j : ℕ) : ℤ) ≤ pairLast r s m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pairStrip_ctx h hr
  clear h
  have hf := fstZ_spec r (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  have hl := lstZ_spec r s (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  simp only [pairFirst, pairLast]
  omega

/-- The discs of the second Hopf letter are first and last attached around it. -/
private theorem pairStrip_bound_hopfSecond {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {m : ℕ}
    (ha : pairTop r s = m ∨ pairTop r s + 1 = m) :
    pairFirst r s m ≤ ((r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 +
        (r - 2) : ℕ) : ℤ) ∧
        ((r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 +
        (r - 2) : ℕ) : ℤ) ≤ pairLast r s m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pairStrip_ctx h hr
  clear h
  have hf := fstZ_spec r (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  have hl := lstZ_spec r s (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  simp only [pairFirst, pairLast]
  omega

/-- The ends of a block attached to `m`. -/
private theorem isoAttached_iff_strip (m : ℕ) (b : SBlock) :
    isoAttached m b = true ↔ (isoEnds b).1 = m ∨ (isoEnds b).2 = m := by
  rw [isoAttached, decide_eq_true_eq]

/-- Every block attached to the disc `m` lies between `pairFirst` and `pairLast`. -/
private theorem pairBlocks_attach_bounds {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r)
    {m k : ℕ} {b : SBlock} (hb : (pairBlocks r s)[k]? = some b) (ha : isoAttached m b = true) :
    pairFirst r s m ≤ k ∧ (k : ℤ) ≤ pairLast r s m := by
  have hk : k < (pairBlocks r s).length := (List.getElem?_eq_some_iff.mp hb).1
  rw [pairBlocks_length] at hk
  rw [isoAttached_iff_strip] at ha
  have key : ∀ x : SBlock, (pairBlocks r s)[k]? = some x → b = x := fun x hx ↦ by
    rw [hb] at hx
    exact Option.some.inj hx
  rcases Nat.lt_or_ge k (r - 2) with h1 | h1
  · cases key _ (pairBlocks_getElem?_climb h1)
    exact pairStrip_bound_climb h hr h1 ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h1
  rcases Nat.lt_or_ge k (pairRunDown r s) with h2 | h2
  · cases key _ (pairBlocks_getElem?_runDown h2)
    exact pairStrip_bound_runDown h hr h2 ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h2
  rw [← Nat.add_assoc] at key ⊢
  rcases Nat.lt_or_ge k (pairRunUp r s) with h3 | h3
  · cases key _ (pairBlocks_getElem?_runUp h3)
    exact pairStrip_bound_runUp h hr h3 ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h3
  rw [← Nat.add_assoc] at key ⊢
  rcases k with _ | _ | _ | k
  · cases key _ pairBlocks_getElem?_bigClimb
    exact pairStrip_bound_bigClimb h hr ha
  · cases key _ pairBlocks_getElem?_roundZero
    exact pairStrip_bound_roundZero h hr ha
  · cases key _ pairBlocks_getElem?_hopfFirst
    exact pairStrip_bound_hopfFirst h hr ha
  rw [show r - 2 + pairRunDown r s + pairRunUp r s + (k + 3) =
    r - 2 + pairRunDown r s + pairRunUp r s + 3 + k by omega] at key ⊢
  rcases Nat.lt_or_ge k (s - 2) with h7 | h7
  · cases key _ (pairBlocks_getElem?_round h7)
    exact pairStrip_bound_round h hr h7 ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h7
  rw [← Nat.add_assoc] at key ⊢
  rcases k with _ | _ | k
  · cases key _ pairBlocks_getElem?_lastRound
    exact pairStrip_bound_lastRound h hr ha
  · cases key _ pairBlocks_getElem?_topRight
    exact pairStrip_bound_topRight h hr ha
  rw [show r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + (k + 2) =
    r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 + k by omega] at key ⊢
  rcases Nat.lt_or_ge k (r - 2) with h10 | h10
  · cases key _ (pairBlocks_getElem?_descent h10)
    exact pairStrip_bound_descent h hr h10 ha
  obtain rfl : k = r - 2 := by omega
  cases key _ (pairBlocks_getElem?_hopfSecond (by omega))
  exact pairStrip_bound_hopfSecond h hr ha

/-- Attachment of a block to a disc, by arithmetic. -/
local macro "strip_att" : tactic =>
  `(tactic| (rw [isoAttached, decide_eq_true_eq]; simp only [isoEnds, true_or, or_true] <;> omega))

/-- The values of `pairFirst` and `pairLast`, by arithmetic. -/
local macro "strip_val" : tactic =>
  `(tactic| (simp only [pairFirst, pairLast]; push_cast; omega))

/-- The block `pairFirst r s m` is attached to the disc `m`. -/
private theorem pairBlocks_attach_first {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {m : ℕ}
    (h1 : 1 ≤ m) (h2 : m ≤ pairTop r s + 1) :
    ∃ (i : ℕ) (b : SBlock), (i : ℤ) = pairFirst r s m ∧ (pairBlocks r s)[i]? = some b ∧
      isoAttached m b = true := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  clear h
  have hf := fstZ_spec r (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  rcases Nat.lt_or_ge m (r - 2) with d | d
  · exact ⟨_, _, by strip_val, pairBlocks_getElem?_climb (s := s) (i := m) d, by strip_att⟩
  rcases Nat.lt_or_ge m (r - 1) with d | d
  · exact ⟨_, _, by strip_val, pairBlocks_getElem?_runDown (j := pairRunDown r s - 1) (by omega),
      by strip_att⟩
  rcases Nat.lt_or_ge m (r + pairRunDown r s - 2) with d | d
  · exact ⟨_, _, by strip_val,
      pairBlocks_getElem?_runDown (j := r + pairRunDown r s - 3 - m) (by omega), by strip_att⟩
  rcases Nat.lt_or_ge m (r + pairRunDown r s - 1) with d | d
  · exact ⟨_, _, by strip_val, pairBlocks_getElem?_runDown (j := 0) (by omega), by strip_att⟩
  rcases Nat.lt_or_ge m (r + pairRunDown r s - 1 + pairRunUp r s) with d | d
  · exact ⟨_, _, by strip_val,
      pairBlocks_getElem?_runUp (j := m + 1 - r - pairRunDown r s) (by omega), by strip_att⟩
  rcases Nat.lt_or_ge m (pairTop r s - r) with d | d
  · exact ⟨_, _, by strip_val, pairBlocks_getElem?_round (j := pairTop r s - r - 1 - m)
      (by omega), by strip_att⟩
  rcases Nat.lt_or_ge m (pairTop r s + 1 - r) with d | d
  · exact ⟨_, _, by strip_val, pairBlocks_getElem?_roundZero, by strip_att⟩
  rcases Nat.lt_or_ge m (pairTop r s + 2 - r) with d | d
  · exact ⟨_, _, by strip_val, pairBlocks_getElem?_bigClimb, by strip_att⟩
  rcases Nat.lt_or_ge m (pairTop r s) with d | d
  · exact ⟨_, _, by strip_val, pairBlocks_getElem?_climb (s := s) (i := pairTop r s - 1 - m)
      (by omega), by strip_att⟩
  rcases Nat.lt_or_ge m (pairTop r s + 1) with d | d
  · exact ⟨_, _, by strip_val, pairBlocks_getElem?_roundZero, by strip_att⟩
  · exact ⟨_, _, by strip_val, pairBlocks_getElem?_hopfFirst, by strip_att⟩

/-- The block `pairLast r s m` is attached to the disc `m`. -/
private theorem pairBlocks_attach_last {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {m : ℕ}
    (h1 : 1 ≤ m) (h2 : m ≤ pairTop r s + 1) :
    ∃ (i : ℕ) (b : SBlock), (i : ℤ) = pairLast r s m ∧ (pairBlocks r s)[i]? = some b ∧
      isoAttached m b = true := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  clear h
  have hl := lstZ_spec r s (pairRunDown r s) (pairRunUp r s) (pairTop r s) m
  rcases Nat.lt_or_ge m (r - 2) with d | d
  · exact ⟨_, _, by strip_val, pairBlocks_getElem?_descent (j := r - 3 - m) (by omega),
      by strip_att⟩
  rcases Nat.lt_or_ge m (r - 1) with d | d
  · exact ⟨_, _, by strip_val, pairBlocks_getElem?_lastRound, by strip_att⟩
  rcases Nat.lt_or_ge m (r + pairRunDown r s - 2) with d | d
  · exact ⟨_, _, by strip_val,
      pairBlocks_getElem?_runDown (j := r + pairRunDown r s - 2 - m) (by omega), by strip_att⟩
  rcases Nat.lt_or_ge m (r + pairRunDown r s - 2 + pairRunUp r s) with d | d
  · exact ⟨_, _, by strip_val,
      pairBlocks_getElem?_runUp (j := m + 2 - r - pairRunDown r s) (by omega), by strip_att⟩
  rcases Nat.lt_or_ge m (r + pairRunDown r s - 1 + pairRunUp r s) with d | d
  · exact ⟨_, _, by strip_val, pairBlocks_getElem?_bigClimb, by strip_att⟩
  rcases Nat.lt_or_ge m (pairTop r s - s) with d | d
  · exact ⟨_, _, by strip_val,
      pairBlocks_getElem?_descent (j := m - (pairTop r s + 2 - s - r)) (by omega), by strip_att⟩
  rcases Nat.lt_or_ge m (pairTop r s + 1 - s) with d | d
  · exact ⟨_, _, by strip_val, pairBlocks_getElem?_topRight, by strip_att⟩
  rcases Nat.lt_or_ge m (pairTop r s + 2 - s) with d | d
  · exact ⟨_, _, by strip_val, pairBlocks_getElem?_lastRound, by strip_att⟩
  rcases Nat.lt_or_ge m (pairTop r s) with d | d
  · exact ⟨_, _, by strip_val, pairBlocks_getElem?_round (j := pairTop r s - 1 - m) (by omega),
      by strip_att⟩
  · exact ⟨_, _, by strip_val, pairBlocks_getElem?_hopfSecond (by omega), by strip_att⟩

/-- The first block of a disc of `pairBlocks r s`. -/
private theorem isoFirst_pairBlocks {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {m : ℕ}
    (h1 : 1 ≤ m) (h2 : m ≤ pairTop r s + 1) :
    (isoFirst (pairBlocks r s) m : ℤ) = pairFirst r s m := by
  obtain ⟨i, b, hi, hb, ha⟩ := pairBlocks_attach_first h hr h1 h2
  have hle := isoFirst_le_of_attached hb ha
  have hlt : isoFirst (pairBlocks r s) m < (pairBlocks r s).length :=
    List.findIdx_lt_length_of_exists ⟨b, List.mem_of_getElem? hb, ha⟩
  have hge := pairBlocks_attach_bounds h hr (List.getElem?_eq_getElem hlt)
    (List.findIdx_getElem (w := hlt))
  omega

/-- The last block of a disc of `pairBlocks r s`. -/
private theorem isoLast_pairBlocks {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {m : ℕ}
    (h1 : 1 ≤ m) (h2 : m ≤ pairTop r s + 1) :
    (isoLast (pairBlocks r s) m : ℤ) = pairLast r s m := by
  obtain ⟨i, b, hi, hb, ha⟩ := pairBlocks_attach_last h hr h1 h2
  have hle := (le_isoLast_of_attached hb ha).1
  have hlt : (pairBlocks r s).reverse.findIdx (isoAttached m) < (pairBlocks r s).reverse.length :=
    List.findIdx_lt_length_of_exists ⟨b, List.mem_reverse.mpr (List.mem_of_getElem? hb), ha⟩
  have hat := List.findIdx_getElem (w := hlt)
  rw [List.getElem_reverse] at hat
  have hge := pairBlocks_attach_bounds h hr (List.getElem?_eq_getElem _) hat
  rw [List.length_reverse] at hlt
  rw [isoLast] at hle ⊢
  omega

/-- Counting a filter over a range: a run of `d` elements that all pass. -/
private theorem length_filter_range_add_true (p : ℕ → Bool) (a d : ℕ)
    (hp : ∀ x, a ≤ x → x < a + d → p x = true) :
    ((List.range (a + d)).filter p).length = ((List.range a).filter p).length + d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc, List.range_succ, List.filter_append, List.length_append,
      ih fun x h1 h2 ↦ hp x h1 (by omega)]
    simp [hp (a + d) (by omega) (by omega)]
    omega

/-- Counting a filter over a range: a run of `d` elements that all fail. -/
private theorem length_filter_range_add_false (p : ℕ → Bool) (a d : ℕ)
    (hp : ∀ x, a ≤ x → x < a + d → p x = false) :
    ((List.range (a + d)).filter p).length = ((List.range a).filter p).length := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc, List.range_succ, List.filter_append, List.length_append,
      ih fun x h1 h2 ↦ hp x h1 (by omega)]
    simp [hp (a + d) (by omega) (by omega)]

/-- Counting a filter over `0, …, m - 1` that fails at `0`, then passes `a` times, fails `d₁`
times, passes `d₂` times and fails `d₃` times. -/
private theorem length_filter_range_five (p : ℕ → Bool) (a d₁ d₂ d₃ : ℕ) (h0 : p 0 = false)
    (h1 : ∀ x, 1 ≤ x → x ≤ a → p x = true) (h2 : ∀ x, a < x → x ≤ a + d₁ → p x = false)
    (h3 : ∀ x, a + d₁ < x → x ≤ a + d₁ + d₂ → p x = true)
    (h4 : ∀ x, a + d₁ + d₂ < x → x ≤ a + d₁ + d₂ + d₃ → p x = false) :
    ((List.range (1 + a + d₁ + d₂ + d₃)).filter p).length = a + d₂ := by
  rw [length_filter_range_add_false p _ _ fun x hx1 hx2 ↦ h4 x (by omega) (by omega),
    length_filter_range_add_true p _ _ fun x hx1 hx2 ↦ h3 x (by omega) (by omega),
    length_filter_range_add_false p _ _ fun x hx1 hx2 ↦ h2 x (by omega) (by omega),
    length_filter_range_add_true p _ _ fun x hx1 hx2 ↦ h1 x (by omega) (by omega)]
  simp [h0]

/-- A disc of `pairBlocks r s` is open at the block `k` when `k` lies between its first and last
block. -/
private theorem isoOpen_pairBlocks {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {k x : ℕ}
    (hx : x ≤ pairTop r s + 1) :
    isoOpen (pairBlocks r s) 0 x k = true ↔
      1 ≤ x ∧ pairFirst r s x ≤ k ∧ (k : ℤ) ≤ pairLast r s x := by
  simp only [isoOpen, decide_eq_true_eq]
  by_cases h1 : 1 ≤ x
  · have e1 := isoFirst_pairBlocks h hr h1 hx
    have e2 := isoLast_pairBlocks h hr h1 hx
    clear h
    constructor
    · rintro ⟨-, h2 | ⟨h3, h4⟩⟩
      · omega
      · exact ⟨h1, by omega, by omega⟩
    · rintro ⟨-, h3, h4⟩
      exact ⟨h1, Or.inr ⟨by omega, by omega⟩⟩
  · constructor
    · rintro ⟨h2, -⟩
      exact absurd h2 h1
    · rintro ⟨h2, -⟩
      exact absurd h2 h1

/-- The position of a disc of `pairBlocks r s` at the block `k`, from the pattern of the open
discs below it: `a` open, `d₁` closed, `d₂` open, `d₃` closed. -/
private theorem isoPos_pairBlocks {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r)
    (k a d₁ d₂ d₃ m : ℕ) (hm : m = 1 + a + d₁ + d₂ + d₃) (hmT : m ≤ pairTop r s + 1)
    (h1 : ∀ x, 1 ≤ x → x ≤ a → pairFirst r s x ≤ k ∧ (k : ℤ) ≤ pairLast r s x)
    (h2 : ∀ x, a < x → x ≤ a + d₁ → ¬ (pairFirst r s x ≤ k ∧ (k : ℤ) ≤ pairLast r s x))
    (h3 : ∀ x, a + d₁ < x → x ≤ a + d₁ + d₂ → pairFirst r s x ≤ k ∧ (k : ℤ) ≤ pairLast r s x)
    (h4 : ∀ x, a + d₁ + d₂ < x → x ≤ a + d₁ + d₂ + d₃ →
      ¬ (pairFirst r s x ≤ k ∧ (k : ℤ) ≤ pairLast r s x)) :
    isoPos (pairBlocks r s) 0 k m = 1 + 2 * (a + d₂) := by
  have hO : ∀ x, x ≤ pairTop r s + 1 → (isoOpen (pairBlocks r s) 0 x k = true ↔
      1 ≤ x ∧ pairFirst r s x ≤ k ∧ (k : ℤ) ≤ pairLast r s x) := fun x hx ↦
    isoOpen_pairBlocks h hr hx
  rw [isoPos, ite_eq_right (by omega), hm, length_filter_range_five _ a d₁ d₂ d₃]
  · exact Bool.eq_false_iff.mpr fun hc ↦ by have := ((hO 0 (by omega)).mp hc).1; omega
  · exact fun x hx1 hx2 ↦ (hO x (by omega)).mpr ⟨hx1, h1 x hx1 hx2⟩
  · exact fun x hx1 hx2 ↦ Bool.eq_false_iff.mpr fun hc ↦
      h2 x hx1 hx2 ((hO x (by omega)).mp hc).2
  · exact fun x hx1 hx2 ↦ (hO x (by omega)).mpr ⟨by omega, h3 x hx1 hx2⟩
  · exact fun x hx1 hx2 ↦ Bool.eq_false_iff.mpr fun hc ↦
      h4 x hx1 hx2 ((hO x (by omega)).mp hc).2

/-- The filter of a range by a predicate true at exactly two points. -/
private theorem filter_range_two (a b : ℕ) (hab : a < b) (p : ℕ → Bool) :
    ∀ N, (∀ x < N, p x = true ↔ x = a ∨ x = b) →
      (List.range N).filter p = (if a < N then [a] else []) ++ (if b < N then [b] else [])
  | 0, _ => rfl
  | N + 1, hp => by
    rw [List.range_succ, List.filter_append,
      filter_range_two a b hab p N fun x hx ↦ hp x (by omega)]
    have hN := hp N (by omega)
    by_cases h1 : N = a
    · subst h1
      simp [hN, show ¬ b < N by omega, show ¬ b < N + 1 by omega]
    by_cases h2 : N = b
    · subst h2
      simp [hN, show a < N by omega, show a < N + 1 by omega]
    have : p N = false := Bool.eq_false_iff.mpr fun hc ↦ by
      rcases hN.mp hc with h | h <;> contradiction
    have e1 : (a < N + 1 ↔ a < N) := by omega
    have e2 : (b < N + 1 ↔ b < N) := by omega
    simp only [List.filter_cons, this, List.filter_nil, e1, e2, Bool.false_eq_true,
      ↓reduceIte, List.append_nil]

/-- The discs opened by the block `k` of `pairBlocks r s`. -/
private theorem decide_isoFirst_pairBlocks {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r)
    {k x : ℕ} (hx : x < pairTop r s + 2) :
    decide (0 < x ∧ isoFirst (pairBlocks r s) x = k) = true ↔ 1 ≤ x ∧ pairFirst r s x = k := by
  rw [decide_eq_true_eq]
  by_cases h1 : 1 ≤ x
  · have e := isoFirst_pairBlocks h hr h1 (by omega)
    clear h
    constructor
    · rintro ⟨-, h2⟩
      exact ⟨h1, by omega⟩
    · rintro ⟨-, h2⟩
      exact ⟨h1, by omega⟩
  · constructor <;> rintro ⟨h2, -⟩ <;> omega

/-- The discs closed by the block `k` of `pairBlocks r s`. -/
private theorem decide_isoLast_pairBlocks {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r)
    {k x : ℕ} (hx : x < pairTop r s + 2) :
    decide (0 < x ∧ isoLast (pairBlocks r s) x = k) = true ↔ 1 ≤ x ∧ pairLast r s x = k := by
  rw [decide_eq_true_eq]
  by_cases h1 : 1 ≤ x
  · have e := isoLast_pairBlocks h hr h1 (by omega)
    clear h
    constructor
    · rintro ⟨-, h2⟩
      exact ⟨h1, by omega⟩
    · rintro ⟨-, h2⟩
      exact ⟨h1, by omega⟩
  · constructor <;> rintro ⟨h2, -⟩ <;> omega

/-- The filter of a range by a predicate true at no point. -/
private theorem filter_range_none (p : ℕ → Bool) (N : ℕ) (hp : ∀ x < N, ¬ p x = true) :
    (List.range N).filter p = [] := by
  rw [filter_range_two N (N + 1) (by omega) p N fun x hx ↦ ⟨fun h ↦ absurd h (hp x hx),
    fun h ↦ by omega⟩]
  simp

/-- The filter of a range by a predicate true at exactly one point. -/
private theorem filter_range_one (p : ℕ → Bool) (N a : ℕ) (ha : a < N)
    (hp : ∀ x < N, p x = true ↔ x = a) : (List.range N).filter p = [a] := by
  rw [filter_range_two a N ha p N fun x hx ↦ ⟨fun h ↦ Or.inl ((hp x hx).mp h),
    fun h ↦ (hp x hx).mpr (by omega)⟩]
  simp [ha]

/-- The filter of a range by a predicate true at exactly two points. -/
private theorem filter_range_pair (p : ℕ → Bool) (N a b : ℕ) (hab : a < b) (hb : b < N)
    (hp : ∀ x < N, p x = true ↔ x = a ∨ x = b) : (List.range N).filter p = [a, b] := by
  rw [filter_range_two a b hab p N hp]
  simp [hb, show a < N by omega]

/-- A fence block of `pairBlocks r s`, from the lists of the discs it opens and closes. -/
private theorem isoFenceBlock_pairBlocks {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r)
    (k : ℕ) (b : SBlock) (O C : List ℕ)
    (hop : (List.range (pairTop r s + 2)).filter
      (fun x ↦ decide (0 < x ∧ isoFirst (pairBlocks r s) x = k)) = O)
    (hcl : (List.range (pairTop r s + 2)).filter
      (fun x ↦ decide (0 < x ∧ isoLast (pairBlocks r s) x = k)) = C) :
    isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0 k b =
      O.map (fun m ↦ isoU (isoPos (pairBlocks r s) 0 k m)) ++
        isoBlockWord (isoPos (pairBlocks r s) 0 k) b ++
        C.reverse.map (fun m ↦ isoN (isoPos (pairBlocks r s) 0 k m)) := by
  have hn : pairStrands r s - 1 + 1 = pairTop r s + 2 := by
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
    simp only [pairStrands]
    omega
  rw [isoFenceBlock, hn, hop, hcl]

/-- An arithmetic claim about the first and last blocks of the discs of an interval. -/
local macro "strip_cl" r:term:max s:term:max : tactic => `(tactic| (
  intro x hx1 hx2
  have hf := fstZ_spec $r (pairRunDown $r $s) (pairRunUp $r $s) (pairTop $r $s) x
  have hl := lstZ_spec $r $s (pairRunDown $r $s) (pairRunUp $r $s) (pairTop $r $s) x
  simp only [pairFirst, pairLast]
  omega))

/-- The discs opened or closed by a block, by arithmetic. -/
local macro "strip_oc" r:term:max s:term:max h:term:max hr:term:max : tactic => `(tactic| (
  intro x hx
  first
  | rw [decide_isoFirst_pairBlocks $h $hr hx]
  | rw [decide_isoLast_pairBlocks $h $hr hx]
  have hf := fstZ_spec $r (pairRunDown $r $s) (pairRunUp $r $s) (pairTop $r $s) x
  have hl := lstZ_spec $r $s (pairRunDown $r $s) (pairRunUp $r $s) (pairTop $r $s) x
  have c := pairStrip_ctx $h $hr
  simp only [pairFirst, pairLast]
  omega))

/-- The band of span one at `0`. -/
private theorem isoBand_zero_one : isoBand 0 1 true = [isoX true 0] := rfl

set_option maxHeartbeats 4000000 in
/-- The first left climb. -/
private theorem isoFenceBlock_pairBlocks_climbZero {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0 (0)
      (SBlock.band 0 (pairTop r s - 1 - 0)) =
      [isoU 1, isoX true 0] := by
  rw [isoFenceBlock_pairBlocks h hr (0) _ [pairTop r s - 1 - 0]
    []
    (filter_range_one _ _ _ (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))
    (filter_range_none _ _ (by strip_oc r s h hr))]
  have P := isoPos_pairBlocks h hr (0)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  clear h
  have p1 : isoPos (pairBlocks r s) 0 (0) (0) = 0 := by
    rw [isoPos]
    exact ite_eq_left (by omega)
  have p2 : isoPos (pairBlocks r s) 0 (0) (pairTop r s - 1 - 0) = 1 := by
    exact (P (0) (pairTop r s - 2) (0) (0) _ (by omega) (by omega) (by strip_cl r s)
        (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  simp only [List.map_cons, List.map_nil, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_nil, isoBlockWord, isoEnds, isoSign, p1, p2, isoBand_zero_one]

set_option maxHeartbeats 4000000 in
/-- A later left climb. -/
private theorem isoFenceBlock_pairBlocks_climb {r s : ℕ} (h : IsTorusPair r s)
    (hr : 3 ≤ r) {i : ℕ} (hi1 : 1 ≤ i) (hi : i < r - 2) :
    isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0 (i)
      (SBlock.band i (pairTop r s - 1 - i)) =
      isoStLC i := by
  rw [isoFenceBlock_pairBlocks h hr (i) _ [i, pairTop r s - 1 - i]
    []
    (filter_range_pair _ _ _ _ (by have := pairStrip_ctx h hr; omega)
      (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))
    (filter_range_none _ _ (by strip_oc r s h hr))]
  have P := isoPos_pairBlocks h hr (i)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  clear h
  have p1 : isoPos (pairBlocks r s) 0 (i) (i) = 2 * i - 1 := by
    exact (P (i - 1) (0) (0) (0) _ (by omega) (by omega) (by strip_cl r s) (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  have p2 : isoPos (pairBlocks r s) 0 (i) (pairTop r s - 1 - i) = 2 * i + 1 := by
    exact (P (i) (pairTop r s - 2 - 2 * i) (0) (0) _ (by omega) (by omega) (by strip_cl r s)
        (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  simp only [List.map_cons, List.map_nil, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_nil, isoBlockWord, isoEnds, isoSign, p1, p2, isoStLC]

set_option maxHeartbeats 4000000 in
/-- The first block of the decreasing run. -/
private theorem isoFenceBlock_pairBlocks_runDownZero {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0 (r - 2 + 0)
      (SBlock.band (r + pairRunDown r s - 3 - 0) (r + pairRunDown r s - 2 - 0)) =
      isoStLC (r - 2) := by
  rw [isoFenceBlock_pairBlocks h hr (r - 2 + 0) _ [r + pairRunDown r s - 3 - 0,
      r + pairRunDown r s - 2 - 0]
    []
    (filter_range_pair _ _ _ _ (by have := pairStrip_ctx h hr; omega)
      (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))
    (filter_range_none _ _ (by strip_oc r s h hr))]
  have P := isoPos_pairBlocks h hr (r - 2 + 0)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  clear h
  have p1 : isoPos (pairBlocks r s) 0 (r - 2 + 0) (r + pairRunDown r s - 3 - 0) =
      2 * (r - 2) - 1 := by
    exact (P (r - 3) (pairRunDown r s - 1) (0) (0) _ (by omega) (by omega) (by strip_cl r s)
        (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  have p2 : isoPos (pairBlocks r s) 0 (r - 2 + 0) (r + pairRunDown r s - 2 - 0) =
      2 * (r - 2) + 1 := by
    exact (P (r - 3) (pairRunDown r s - 1) (1) (0) _ (by omega) (by omega) (by strip_cl r s)
        (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  simp only [List.map_cons, List.map_nil, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_nil, isoBlockWord, isoEnds, isoSign, p1, p2, isoStLC]

set_option maxHeartbeats 4000000 in
/-- A later block of the decreasing run. -/
private theorem isoFenceBlock_pairBlocks_runDown {r s : ℕ} (h : IsTorusPair r s)
    (hr : 3 ≤ r) {j : ℕ} (hj1 : 1 ≤ j) (hj : j < pairRunDown r s) :
    isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0 (r - 2 + j)
      (SBlock.band (r + pairRunDown r s - 3 - j) (r + pairRunDown r s - 2 - j)) =
      isoStDec (r - 2) := by
  rw [isoFenceBlock_pairBlocks h hr (r - 2 + j) _ [r + pairRunDown r s - 3 - j]
    [r + pairRunDown r s - 2 - j]
    (filter_range_one _ _ _ (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))
    (filter_range_one _ _ _ (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))]
  have P := isoPos_pairBlocks h hr (r - 2 + j)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  clear h
  have p1 : isoPos (pairBlocks r s) 0 (r - 2 + j) (r + pairRunDown r s - 3 - j) =
      2 * (r - 2) - 1 := by
    exact (P (r - 3) (pairRunDown r s - 1 - j) (0) (0) _ (by omega) (by omega) (by strip_cl r s)
        (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  have p2 : isoPos (pairBlocks r s) 0 (r - 2 + j) (r + pairRunDown r s - 2 - j) =
      2 * (r - 2) + 1 := by
    exact (P (r - 3) (pairRunDown r s - 1 - j) (1) (0) _ (by omega) (by omega) (by strip_cl r s)
        (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, isoBlockWord, isoEnds, isoSign, p1, p2, isoStDec]

set_option maxHeartbeats 4000000 in
/-- A block of the increasing run. -/
private theorem isoFenceBlock_pairBlocks_runUp {r s : ℕ} (h : IsTorusPair r s)
    (hr : 3 ≤ r) {j : ℕ} (hj : j < pairRunUp r s) :
    isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0 (r - 2 + pairRunDown r s + j)
      (SBlock.band (r - 2 + pairRunDown r s + j) (r - 1 + pairRunDown r s + j)) =
      isoStInc (r - 2) := by
  rw [isoFenceBlock_pairBlocks h hr (r - 2 + pairRunDown r s + j) _ [r - 1 + pairRunDown r s + j]
    [r - 2 + pairRunDown r s + j]
    (filter_range_one _ _ _ (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))
    (filter_range_one _ _ _ (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))]
  have P := isoPos_pairBlocks h hr (r - 2 + pairRunDown r s + j)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  clear h
  have p1 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + j)
      (r - 2 + pairRunDown r s + j) = 2 * (r - 2) + 1 := by
    exact (P (r - 2) (pairRunDown r s + j - 1) (0) (0) _ (by omega) (by omega) (by strip_cl r s)
        (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  have p2 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + j)
      (r - 1 + pairRunDown r s + j) = 2 * (r - 2) + 3 := by
    exact (P (r - 2) (pairRunDown r s + j - 1) (1) (0) _ (by omega) (by omega) (by strip_cl r s)
        (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, isoBlockWord, isoEnds, isoSign, p1, p2, isoStInc]

set_option maxHeartbeats 4000000 in
/-- The big climb. -/
private theorem isoFenceBlock_pairBlocks_bigClimb {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s)
      (SBlock.band (r - 2 + pairRunDown r s + pairRunUp r s) (pairTop r s + 1 - r)) =
      isoStInc (r - 2) := by
  rw [isoFenceBlock_pairBlocks h hr
      (r - 2 + pairRunDown r s + pairRunUp r s) _ [pairTop r s + 1 - r]
    [r - 2 + pairRunDown r s + pairRunUp r s]
    (filter_range_one _ _ _ (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))
    (filter_range_one _ _ _ (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))]
  have P := isoPos_pairBlocks h hr (r - 2 + pairRunDown r s + pairRunUp r s)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  clear h
  have p1 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s)
      (r - 2 + pairRunDown r s + pairRunUp r s) = 2 * (r - 2) + 1 := by
    exact (P (r - 2) (pairRunDown r s + pairRunUp r s - 1) (0) (0) _ (by omega) (by omega)
        (by strip_cl r s) (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  have p2 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s)
      (pairTop r s + 1 - r) = 2 * (r - 2) + 3 := by
    exact (P (r - 2) (pairRunDown r s + pairRunUp r s - 1) (1) (s - 1) _ (by omega) (by omega)
        (by strip_cl r s) (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, isoBlockWord, isoEnds, isoSign, p1, p2, isoStInc]

set_option maxHeartbeats 4000000 in
/-- Round `0`. -/
private theorem isoFenceBlock_pairBlocks_roundZero {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0
        (r - 2 + pairRunDown r s + pairRunUp r s + 1)
      (SBlock.band (pairTop r s - r) (pairTop r s)) =
      isoStR0 (r - 2) r := by
  rw [isoFenceBlock_pairBlocks h hr
      (r - 2 + pairRunDown r s + pairRunUp r s + 1) _ [pairTop r s - r, pairTop r s]
    []
    (filter_range_pair _ _ _ _ (by have := pairStrip_ctx h hr; omega)
      (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))
    (filter_range_none _ _ (by strip_oc r s h hr))]
  have P := isoPos_pairBlocks h hr (r - 2 + pairRunDown r s + pairRunUp r s + 1)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  clear h
  have p1 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s + 1)
      (pairTop r s - r) = 2 * (r - 2) + 1 := by
    exact (P (r - 2) (pairTop r s - 2 * r + 1) (0) (0) _ (by omega) (by omega) (by strip_cl r s)
        (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  have p2 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s + 1)
      (pairTop r s) = 2 * (r - 2) + 1 + 2 * r := by
    exact (P (r - 2) (pairTop r s - 2 * r + 1) (r) (0) _ (by omega) (by omega) (by strip_cl r s)
        (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  simp only [List.map_cons, List.map_nil, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_nil, isoBlockWord, isoEnds, isoSign, p1, p2, isoStR0]

set_option maxHeartbeats 4000000 in
/-- The first Hopf letter. -/
private theorem isoFenceBlock_pairBlocks_hopfFirst {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0
        (r - 2 + pairRunDown r s + pairRunUp r s + 2)
      (SBlock.neg (pairTop r s)) =
      isoStHopf (r - 2) r := by
  rw [isoFenceBlock_pairBlocks h hr
      (r - 2 + pairRunDown r s + pairRunUp r s + 2) _ [pairTop r s + 1]
    []
    (filter_range_one _ _ _ (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))
    (filter_range_none _ _ (by strip_oc r s h hr))]
  have P := isoPos_pairBlocks h hr (r - 2 + pairRunDown r s + pairRunUp r s + 2)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  clear h
  have p1 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s + 2)
      (pairTop r s) = 2 * (r - 2) + 1 + 2 * r := by
    exact (P (r - 2) (pairTop r s - 2 * r + 1) (r) (0) _ (by omega) (by omega) (by strip_cl r s)
        (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  have p2 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s + 2)
      (pairTop r s + 1) = 2 * (r - 2) + 3 + 2 * r := by
    exact (P (r - 2) (pairTop r s - 2 * r + 1) (r + 1) (0) _ (by omega) (by omega)
        (by strip_cl r s) (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  simp only [List.map_cons, List.map_nil, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_nil, isoBlockWord, isoEnds, isoSign, p1, p2, isoStHopf]

set_option maxHeartbeats 4000000 in
/-- A middle round. -/
private theorem isoFenceBlock_pairBlocks_round {r s : ℕ} (h : IsTorusPair r s)
    (hr : 3 ≤ r) {j : ℕ} (hj : j < s - 2) :
    isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0
        (r - 2 + pairRunDown r s + pairRunUp r s + 3 + j)
      (SBlock.band (pairTop r s - r - 1 - j) (pairTop r s - 1 - j)) =
      isoStRound (r - 2) r := by
  rw [isoFenceBlock_pairBlocks h hr
      (r - 2 + pairRunDown r s + pairRunUp r s + 3 + j) _ [pairTop r s - r - 1 - j]
    [pairTop r s - 1 - j]
    (filter_range_one _ _ _ (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))
    (filter_range_one _ _ _ (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))]
  have P := isoPos_pairBlocks h hr (r - 2 + pairRunDown r s + pairRunUp r s + 3 + j)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  clear h
  have p1 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s + 3 + j)
      (pairTop r s - r - 1 - j) = 2 * (r - 2) + 1 := by
    exact (P (r - 2) (pairTop r s - 2 * r - j) (0) (0) _ (by omega) (by omega) (by strip_cl r s)
        (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  have p2 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s + 3 + j)
      (pairTop r s - 1 - j) = 2 * (r - 2) + 1 + 2 * r := by
    exact (P (r - 2) (pairTop r s - 2 * r - j) (r) (0) _ (by omega) (by omega) (by strip_cl r s)
        (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, isoBlockWord, isoEnds, isoSign, p1, p2, isoStRound]

set_option maxHeartbeats 4000000 in
/-- The last round. -/
private theorem isoFenceBlock_pairBlocks_lastRound {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0
        (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2))
      (SBlock.band (r - 2) (pairTop r s + 1 - s)) =
      isoStLast (r - 2) r := by
  rw [isoFenceBlock_pairBlocks h hr (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2)) _ []
    [r - 2, pairTop r s + 1 - s]
    (filter_range_none _ _ (by strip_oc r s h hr))
    (filter_range_pair _ _ _ _ (by have := pairStrip_ctx h hr; omega)
      (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))]
  have P := isoPos_pairBlocks h hr (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2))
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  clear h
  have p1 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2))
      (r - 2) = 2 * (r - 2) - 1 := by
    exact (P (r - 3) (0) (0) (0) _ (by omega) (by omega) (by strip_cl r s) (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  have p2 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2))
      (pairTop r s + 1 - s) = 2 * (r - 2) - 1 + 2 * r := by
    exact (P (r - 2) (pairTop r s + 3 - s - 2 * r) (r - 1) (0) _ (by omega) (by omega)
        (by strip_cl r s) (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, isoBlockWord, isoEnds, isoSign, p1, p2, isoStLast]

set_option maxHeartbeats 4000000 in
/-- The top-right climb. -/
private theorem isoFenceBlock_pairBlocks_topRight {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0
        (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 1)
      (SBlock.band (pairTop r s - s) (pairTop r s)) =
      isoStTrc (r - 2) := by
  rw [isoFenceBlock_pairBlocks h hr (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 1) _ []
    [pairTop r s - s]
    (filter_range_none _ _ (by strip_oc r s h hr))
    (filter_range_one _ _ _ (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))]
  have P := isoPos_pairBlocks h hr (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 1)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  clear h
  have p1 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 1)
      (pairTop r s - s) = 4 * (r - 2) - 1 := by
    exact (P (r - 3) (pairTop r s + 4 - s - 2 * r) (r - 2) (0) _ (by omega) (by omega)
        (by strip_cl r s) (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  have p2 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 1)
      (pairTop r s) = 4 * (r - 2) + 1 := by
    exact (P (r - 3) (pairTop r s + 4 - s - 2 * r) (r - 1) (s - 1) _ (by omega) (by omega)
        (by strip_cl r s) (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      isoBlockWord, isoEnds, isoSign, p1, p2, isoStTrc]

set_option maxHeartbeats 4000000 in
/-- A right descent to a disc `i ≥ 1`. -/
private theorem isoFenceBlock_pairBlocks_descent {r s : ℕ} (h : IsTorusPair r s)
    (hr : 3 ≤ r) {j : ℕ} (hj : j < r - 3) :
    isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0
        (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 + j)
      (SBlock.band (r - 3 - j) (pairTop r s + 2 - s - r + j)) =
      isoStRd (r - 3 - j) := by
  rw [isoFenceBlock_pairBlocks h hr (r - 2 + pairRunDown r s + pairRunUp r s + 3 +
      (s - 2) + 2 + j) _ []
    [r - 3 - j, pairTop r s + 2 - s - r + j]
    (filter_range_none _ _ (by strip_oc r s h hr))
    (filter_range_pair _ _ _ _ (by have := pairStrip_ctx h hr; omega)
      (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))]
  have P := isoPos_pairBlocks h hr (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 + j)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  clear h
  have p1 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s + 3 +
      (s - 2) + 2 + j) (r - 3 - j) = 2 * (r - 3 - j) - 1 := by
    exact (P (r - 4 - j) (0) (0) (0) _ (by omega) (by omega) (by strip_cl r s) (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  have p2 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s + 3 +
      (s - 2) + 2 + j) (pairTop r s + 2 - s - r + j) = 2 * (r - 3 - j) + 1 := by
    exact (P (r - 3 - j) (pairTop r s + 4 - s - 2 * r + 2 * j) (0) (0) _ (by omega) (by omega)
        (by strip_cl r s) (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, isoBlockWord, isoEnds, isoSign, p1, p2, isoStRd]

set_option maxHeartbeats 4000000 in
/-- The right descent to the disc `0`. -/
private theorem isoFenceBlock_pairBlocks_descentZero {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0
        (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 + (r - 3))
      (SBlock.band (r - 3 - (r - 3)) (pairTop r s + 2 - s - r + (r - 3))) =
      isoStRd0 := by
  rw [isoFenceBlock_pairBlocks h hr (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 +
      (r - 3)) _ []
    [pairTop r s + 2 - s - r + (r - 3)]
    (filter_range_none _ _ (by strip_oc r s h hr))
    (filter_range_one _ _ _ (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))]
  have P := isoPos_pairBlocks h hr (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 +
      (r - 3))
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  clear h
  have p1 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 +
      (r - 3)) (r - 3 - (r - 3)) = 0 := by
    rw [isoPos]
    exact ite_eq_left (by omega)
  have p2 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 +
      (r - 3)) (pairTop r s + 2 - s - r + (r - 3)) = 1 := by
    exact (P (0) (pairTop r s - s - 2) (0) (0) _ (by omega) (by omega) (by strip_cl r s)
        (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, isoBlockWord, isoEnds, isoSign, p1, p2, isoStRd0, isoBand_zero_one]

set_option maxHeartbeats 4000000 in
/-- The second Hopf letter. -/
private theorem isoFenceBlock_pairBlocks_hopfSecond {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0
        (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 + (r - 2))
      (SBlock.neg (pairTop r s)) =
      isoStFinal := by
  rw [isoFenceBlock_pairBlocks h hr (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 +
      (r - 2)) _ []
    [pairTop r s, pairTop r s + 1]
    (filter_range_none _ _ (by strip_oc r s h hr))
    (filter_range_pair _ _ _ _ (by have := pairStrip_ctx h hr; omega)
      (by have := pairStrip_ctx h hr; omega) (by strip_oc r s h hr))]
  have P := isoPos_pairBlocks h hr (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 +
      (r - 2))
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  clear h
  have p1 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 +
      (r - 2)) (pairTop r s) = 1 := by
    exact (P (0) (pairTop r s - 1) (0) (0) _ (by omega) (by omega) (by strip_cl r s)
        (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  have p2 : isoPos (pairBlocks r s) 0 (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 +
      (r - 2)) (pairTop r s + 1) = 3 := by
    exact (P (0) (pairTop r s - 1) (1) (0) _ (by omega) (by omega) (by strip_cl r s)
        (by strip_cl r s)
      (by strip_cl r s) (by strip_cl r s)).trans (by omega)
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, isoBlockWord, isoEnds, isoSign, p1, p2, isoStFinal]

/-- A `flatMap` over an indexed list, as a `flatMap` over the range of its indices. -/
private theorem flatMap_zipIdx_eq_range {α β : Type} (d : α) (F : α × ℕ → List β) :
    ∀ (l : List α) (n : ℕ), (l.zipIdx n).flatMap F =
      (List.range l.length).flatMap (fun k ↦ F ((l[k]?).getD d, n + k))
  | [], _ => rfl
  | a :: l, n => by
    rw [List.zipIdx_cons, List.flatMap_cons, flatMap_zipIdx_eq_range d F l (n + 1),
      List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.getElem?_cons_zero, Option.getD_some, Nat.add_zero, Nat.succ_eq_add_one,
      List.getElem?_cons_succ]
    congr 1
    refine List.flatMap_congr fun k _ ↦ ?_
    rw [show n + 1 + k = n + (k + 1) by omega]

/-- A `flatMap` of a constant word over a range. -/
private theorem flatMap_range_const (X : MorseWord) :
    ∀ (L : ℕ) (f : ℕ → MorseWord), (∀ j < L, f j = X) → (List.range L).flatMap f = phaseTwoBlk X L
  | 0, _, _ => rfl
  | L + 1, f, hf => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_const X L f fun j hj ↦ hf j (by omega),
      List.flatMap_cons, List.flatMap_nil, List.append_nil, hf L (by omega), phaseTwoBlk,
      phaseTwoBlk, List.replicate_succ', List.flatten_append]
    simp

/-- The fence block of `pairBlocks r s` at the index `k`. -/
private def pairFenceAt (r s k : ℕ) : MorseWord :=
  isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0 k (((pairBlocks r s)[k]?).getD (.neg 0))

/-- The fence block at an index with a known block. -/
private theorem pairFenceAt_eq {r s k : ℕ} {b : SBlock} (hb : (pairBlocks r s)[k]? = some b) :
    pairFenceAt r s k = isoFenceBlock (pairStrands r s - 1) (pairBlocks r s) 0 k b := by
  rw [pairFenceAt, hb, Option.getD_some]

/-- The fence word of `pairBlocks r s` block by block. -/
private theorem isoFenceWord_eq_flatMap (r s : ℕ) :
    isoFenceWord (pairStrands r s - 1) (pairBlocks r s) =
      (List.range (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 + (r - 2) + 1)).flatMap
        (pairFenceAt r s) := by
  rw [isoFenceWord, isoFenceAux, Nat.zero_min, List.range_zero, List.map_nil, List.nil_append,
    List.reverse_nil, List.map_nil, List.append_nil, flatMap_zipIdx_eq_range (.neg 0),
    pairBlocks_length]
  simp only [Nat.zero_add]
  rfl

/-- The fence word of the left climbs. -/
private theorem pairFence_climbs {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    (List.range (r - 2)).flatMap (pairFenceAt r s) =
      [isoU 1, isoX true 0] ++ (List.range (r - 2 - 1)).flatMap (fun i ↦ isoStLC (i + 1)) := by
  rw [show List.range (r - 2) = List.range (1 + (r - 2 - 1)) from congrArg _ (by omega),
    List.range_add, List.flatMap_append, List.flatMap_map]
  congr 1
  · simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [pairFenceAt_eq (pairBlocks_getElem?_climb (s := s) (i := 0) (by omega)),
      isoFenceBlock_pairBlocks_climbZero h hr]
  · refine List.flatMap_congr fun i hi ↦ ?_
    rw [List.mem_range] at hi
    rw [pairFenceAt_eq (pairBlocks_getElem?_climb (s := s) (i := 1 + i) (by omega)),
      isoFenceBlock_pairBlocks_climb h hr (by omega) (by omega), Nat.add_comm]

/-- The fence word of the decreasing run. -/
private theorem pairFence_runDown {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    ((List.range (pairRunDown r s)).map (r - 2 + ·)).flatMap (pairFenceAt r s) =
      isoStLC (r - 2) ++ phaseTwoBlk (isoStDec (r - 2)) (pairRunDown r s - 1) := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairStrip_ctx h hr
  rw [show pairRunDown r s = 1 + (pairRunDown r s - 1) by omega, List.range_add,
    List.map_append, List.flatMap_append, List.map_map, show 1 + (pairRunDown r s - 1) - 1 =
      pairRunDown r s - 1 by omega]
  congr 1
  · simp only [List.range_one, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rw [pairFenceAt_eq (pairBlocks_getElem?_runDown (r := r) (s := s) (j := 0) (by omega)),
      isoFenceBlock_pairBlocks_runDownZero h hr]
  · rw [List.flatMap_map]
    refine flatMap_range_const _ _ _ fun j hj ↦ ?_
    simp only [Function.comp_apply]
    rw [pairFenceAt_eq (pairBlocks_getElem?_runDown (r := r) (s := s) (j := 1 + j) (by omega)),
      isoFenceBlock_pairBlocks_runDown h hr (by omega) (by omega)]

/-- The fence word of the increasing run. -/
private theorem pairFence_runUp {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    ((List.range (pairRunUp r s)).map (r - 2 + pairRunDown r s + ·)).flatMap (pairFenceAt r s) =
      phaseTwoBlk (isoStInc (r - 2)) (pairRunUp r s) := by
  rw [List.flatMap_map]
  refine flatMap_range_const _ _ _ fun j hj ↦ ?_
  rw [pairFenceAt_eq (pairBlocks_getElem?_runUp hj), isoFenceBlock_pairBlocks_runUp h hr hj]

/-- The fence word of the big climb, round `0` and the first Hopf letter. -/
private theorem pairFence_middle {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    ((List.range 3).map (r - 2 + pairRunDown r s + pairRunUp r s + ·)).flatMap (pairFenceAt r s) =
      isoStInc (r - 2) ++ isoStR0 (r - 2) r ++ isoStHopf (r - 2) r := by
  simp only [show List.range 3 = [0, 1, 2] from rfl, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero, List.append_assoc]
  rw [pairFenceAt_eq pairBlocks_getElem?_bigClimb, isoFenceBlock_pairBlocks_bigClimb h hr,
    pairFenceAt_eq pairBlocks_getElem?_roundZero, isoFenceBlock_pairBlocks_roundZero h hr,
    pairFenceAt_eq pairBlocks_getElem?_hopfFirst, isoFenceBlock_pairBlocks_hopfFirst h hr]

/-- The fence word of the middle rounds. -/
private theorem pairFence_rounds {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    ((List.range (s - 2)).map (r - 2 + pairRunDown r s + pairRunUp r s + 3 + ·)).flatMap
      (pairFenceAt r s) = phaseTwoBlk (isoStRound (r - 2) r) (s - 2) := by
  rw [List.flatMap_map]
  refine flatMap_range_const _ _ _ fun j hj ↦ ?_
  rw [pairFenceAt_eq (pairBlocks_getElem?_round hj), isoFenceBlock_pairBlocks_round h hr hj]

/-- The fence word of the last round and the top-right climb. -/
private theorem pairFence_top {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    ((List.range 2).map (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + ·)).flatMap
      (pairFenceAt r s) = isoStLast (r - 2) r ++ isoStTrc (r - 2) := by
  simp only [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero]
  rw [pairFenceAt_eq pairBlocks_getElem?_lastRound, isoFenceBlock_pairBlocks_lastRound h hr,
    pairFenceAt_eq pairBlocks_getElem?_topRight, isoFenceBlock_pairBlocks_topRight h hr]

/-- The fence word of the right descents. -/
private theorem pairFence_descents {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    ((List.range (r - 2)).map (r - 2 + pairRunDown r s + pairRunUp r s + 3 +
        (s - 2) + 2 + ·)).flatMap
      (pairFenceAt r s) =
      (List.range (r - 2 - 1)).reverse.flatMap (fun i ↦ isoStRd (i + 1)) ++ isoStRd0 := by
  rw [show List.range (r - 2) = List.range (r - 3 + 1) from congrArg _ (by omega),
    List.range_succ, List.map_append, List.flatMap_append, show r - 2 - 1 = r - 3 by omega]
  congr 1
  · rw [List.flatMap_map, List.range_eq_range', List.reverse_range', ← List.range_eq_range',
      List.flatMap_map]
    refine List.flatMap_congr fun j hj ↦ ?_
    rw [List.mem_range] at hj
    rw [pairFenceAt_eq (pairBlocks_getElem?_descent (r := r) (s := s) (j := j) (by omega)),
      isoFenceBlock_pairBlocks_descent h hr hj, show 0 + (r - 3) - 1 - j + 1 = r - 3 - j by omega]
  · simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [pairFenceAt_eq (pairBlocks_getElem?_descent (r := r) (s := s) (j := r - 3) (by omega)),
      isoFenceBlock_pairBlocks_descentZero h hr]

/-- The fence word of the second Hopf letter. -/
private theorem pairFence_final {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    ((List.range 1).map (r - 2 + pairRunDown r s + pairRunUp r s + 3 + (s - 2) + 2 +
        (r - 2) + ·)).flatMap
      (pairFenceAt r s) = isoStFinal := by
  simp only [List.range_one, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Nat.add_zero]
  rw [pairFenceAt_eq (pairBlocks_getElem?_hopfSecond (by omega)),
    isoFenceBlock_pairBlocks_hopfSecond h hr]

/-- The fence word of `pairBlocks r s` in closed form. -/
theorem isoFenceWord_pairBlocks {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    isoFenceWord (pairStrands r s - 1) (pairBlocks r s) = pairStrip r s := by
  have hInc : phaseTwoBlk (isoStInc (r - 2)) (pairRunUp r s + 1) =
      phaseTwoBlk (isoStInc (r - 2)) (pairRunUp r s) ++ isoStInc (r - 2) := by
    simp [phaseTwoBlk, List.replicate_succ', List.flatten_append]
  rw [isoFenceWord_eq_flatMap]
  repeat rw [List.range_add, List.flatMap_append]
  rw [pairFence_climbs h hr, pairFence_runDown h hr, pairFence_runUp h hr, pairFence_middle h hr,
    pairFence_rounds h hr, pairFence_top h hr, pairFence_descents h hr, pairFence_final h hr,
    pairStrip, hInc]
  simp only [List.append_assoc]

/-- Phase I: the long closure of `pairWhiteheadWord r s` reaches the strip word. -/
theorem morseReach_pair_source_strip {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (morseLongClosure (pairStrands r s) (pairWhiteheadWord r s)) (pairStrip r s) := by
  have h1 := morseReach_isoPhaseOne (isoFenceable_pairBlocks h)
  rwa [isoFenceWord_pairBlocks h hr, show pairStrands r s - 1 + 1 = pairStrands r s by
    simp [pairStrands]] at h1

end AJConjecture
