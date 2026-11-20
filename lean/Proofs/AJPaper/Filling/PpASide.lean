import Mathlib
import AJHandoff.TorusKnot.PairKAnnArith
import AJHandoff.TorusKnot.PairKRevGapConv
import AJTwist.Knot.TwKBlocks

/-!
# The two sides of the head band on the annulus path (PpA, crux)

Source: arXiv:2611.24826v1, Section 2 (`marking.tex`): "The disk twist on the axis side fixes
`λ_A` and sends `μ_A` to `μ_A λ_A`": a full twist of the band conjugates the meridians on one
side of the twist site by the axis longitude. For the braided annulus of
`AJHandoff.TorusKnot.PairKBlocks` the twist site is the head band `b(0, j₀)`
(`j₀ = twHeadTop r s`), and "one side" is made precise as follows.

The annulus bands of `pairBlocks r s` form one cycle through the levels `0, …, 2c - 1`; without
the top-right climb `C = b(T - s, T)` (`T = 2c - 1`) they form a path from `T` to `T - s`
(`AJHandoff.TorusKnot.PairKAnnDefs`). Removing also the head band cuts the path into the part
from `T` to the level `0` and the part from `j₀` to `T - s`. `ppaSide r s n` says that the level
`n` lies on the second part:

* a top level `T - t` (`t ≤ s + r - 2`): its chain index `i(t) = pairAnnIdx r s t` is at least
  the chain index `i(1)` of `T - 1` (for `r ≥ 3`, `j₀ = T - 1`; the chains are visited in the
  order of their index);
* a bottom level `n < r - 2` (between `T - (s+1+n)` and `T - (n+1)` on the path):
  `i(n + 1) > i(1)`;
* a run level `r - 2 ≤ n ≤ 2c - s - r` (between `T - (s-1)` and `T - (r-1)`):
  `i(r - 1) > i(1)` for `r ≥ 3`; for `r = 2` the head band is the first run letter `b(0, 1)` and
  the second part contains the run levels `n ≥ 1`.

* `ppaSide_ends`: `0` and `T` are on the first part, `j₀` and `T - s` on the second;
* `ppaSide_band`: every block of `pairBlocks r s` other than the head band, `C` and the two
  Hopf letters is a band `b(i, j)` with `j ≤ T` whose two levels are on the same part.

Route for `ppaSide_band`: the block at position `q` is `pairBlkRv r s q`
(`pairBlocks_getDRv`), explicit in each of the regimes of `pairBlkAt_reg1Rv`–`reg11Rv`
(`AJHandoff.TorusKnot.PairKRevGapConv`):
left climbs `b(n, T - (n+1))`, `1 ≤ n ≤ r - 3`: `i(n+1) ≠ i(1)` as `n + 1 ≢ 1 (mod r)`
(`pairAnnIdx_unique`); the runs join run levels; the big climb `b(2c-s-r, T - (r-1))`:
`i(r-1) ≠ i(1)` for `r ≥ 3`, and for `r = 2` both levels are on the second part; the rounds
`b(T - (τ+r), T - τ)`: `i(τ + r) = i(τ)` (`pairAnn_chain`); the last round `b(r-2, T - (s-1))`
and the right descents `b(n, T - (s+1+n))`: `i(t + s) = i(t) - 1` when `i(t) ≥ 1`
(`pairAnnIdx_unique`), with `t = r - 1` resp. `t = n + 1`. For `r = 2` there are no bottom
levels, `i(t) = t mod 2` and `i(1) = 1`.

Checked for all 88 coprime pairs with `r ≤ 9`, `s ≤ 23` (`SCR/A/py/exact.py`, `check_sides`: the
formula is reachability from `j₀` in the graph of the remaining bands), and on the Lean
definition for the pairs with `r ≤ 5`, `s ≤ 9` (`SCR/A/lean/TestSide.lean`).
-/

namespace AJConjecture

/-- The level `n < 2c` of the braided annulus lies beyond the head band on the path from the
top level `T = 2c - 1` to `T - s`. -/
def ppaSide (r s n : ℕ) : Bool :=
  if n < r - 2 then decide (pairAnnIdx r s 1 < pairAnnIdx r s (n + 1))
  else if n ≤ pairIdxB r s then
    if r = 2 then decide (1 ≤ n) else decide (pairAnnIdx r s 1 < pairAnnIdx r s (r - 1))
  else decide (pairAnnIdx r s 1 ≤ pairAnnIdx r s (2 * pairC r s - 1 - n))

/-- The chain index of `0 < t < r` is positive. -/
private theorem pairAnnIdx_pos_ppaSide {r s : ℕ} (h : IsTorusPair r s) {t : ℕ} (h0 : 0 < t)
    (ht : t < r) : 0 < pairAnnIdx r s t := by
  rcases Nat.eq_zero_or_pos (pairAnnIdx r s t) with h1 | h1
  · have := (pairAnnIdx_spec h t).2
    rw [h1, zero_mul, add_zero, Nat.mod_eq_of_lt ht] at this
    omega
  · exact h1

/-- `i(t + s) = i(t) - 1` when `i(t) ≥ 1`. -/
private theorem pairAnnIdx_add_ppaSide {r s : ℕ} (h : IsTorusPair r s) {t : ℕ}
    (h0 : 0 < pairAnnIdx r s t) : pairAnnIdx r s (t + s) + 1 = pairAnnIdx r s t := by
  have hi := pairAnnIdx_spec h t
  obtain ⟨i, hieq⟩ : ∃ i, pairAnnIdx r s t = i + 1 := ⟨pairAnnIdx r s t - 1, by omega⟩
  rw [hieq] at hi ⊢
  rw [pairAnnIdx_unique h (i := i) (by omega) (by rw [← hi.2]; congr 1; ring)]

/-- The chain index is injective on `t < r`. -/
private theorem pairAnnIdx_inj_ppaSide {r s : ℕ} (h : IsTorusPair r s) {t t' : ℕ} (ht : t < r)
    (ht' : t' < r) (he : pairAnnIdx r s t = pairAnnIdx r s t') : t = t' := by
  have h1 := (pairAnnIdx_spec h t).2
  have h2 := (pairAnnIdx_spec h t').2
  rw [he] at h1
  have hm : t + pairAnnIdx r s t' * s ≡ t' + pairAnnIdx r s t' * s [MOD r] := h1.trans h2.symm
  have := Nat.ModEq.add_right_cancel' _ hm
  rwa [Nat.ModEq, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at this

/-- The side of a bottom level. -/
private theorem ppaSide_bot_ppaSide {r s n : ℕ} (hn : n < r - 2) :
    ppaSide r s n = decide (pairAnnIdx r s 1 < pairAnnIdx r s (n + 1)) := by
  rw [ppaSide, ite_eq_left hn]

/-- The side of a run level. -/
private theorem ppaSide_run_ppaSide {r s n : ℕ} (h1 : r - 2 ≤ n) (h2 : n ≤ pairIdxB r s) :
    ppaSide r s n =
      if r = 2 then decide (1 ≤ n) else decide (pairAnnIdx r s 1 < pairAnnIdx r s (r - 1)) := by
  rw [ppaSide, ite_eq_right (by omega), ite_eq_left h2]

/-- The side of the top level `T - t`. -/
private theorem ppaSide_top_ppaSide {r s : ℕ} (h : IsTorusPair r s) {n t : ℕ}
    (ht : t ≤ s + r - 2) (hn : n + t = 2 * pairC r s - 1) :
    ppaSide r s n = decide (pairAnnIdx r s 1 ≤ pairAnnIdx r s t) := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  have hB := pairRev_idxB h
  rw [ppaSide, ite_eq_right (by omega), ite_eq_right (by omega),
    show 2 * pairC r s - 1 - n = t by omega]

/-- Two run levels are on the same side. -/
private theorem ppaSide_run_eq_ppaSide {r s n n' : ℕ} (h1 : r - 2 ≤ n)
    (h2 : n ≤ pairIdxB r s) (h1' : r - 2 ≤ n') (h2' : n' ≤ pairIdxB r s)
    (hn : r = 2 → (1 ≤ n ↔ 1 ≤ n')) : ppaSide r s n = ppaSide r s n' := by
  rw [ppaSide_run_ppaSide h1 h2, ppaSide_run_ppaSide h1' h2']
  by_cases hr : r = 2
  · rw [ite_eq_left hr, ite_eq_left hr, decide_eq_decide]
    exact hn hr
  · rw [ite_eq_right hr, ite_eq_right hr]

/-- The ends of the two parts of the path. -/
theorem ppaSide_ends {r s : ℕ} (h : IsTorusPair r s) :
    ppaSide r s 0 = false ∧ ppaSide r s (twHeadTop r s) = true ∧
      ppaSide r s (2 * pairC r s - 1) = false ∧ ppaSide r s (2 * pairC r s - 1 - s) = true := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  have hB := pairRev_idxB h
  have hi1 := pairAnnIdx_pos_ppaSide h (t := 1) (by omega) (by omega)
  have hi1r := (pairAnnIdx_spec h 1).1
  have hi0 : pairAnnIdx r s 0 = 0 := pairAnnIdx_unique h (by omega) (by simp)
  have his : pairAnnIdx r s s = r - 1 := by
    refine pairAnnIdx_unique h (by omega) ?_
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel, show s + r' * s = (r' + 1) * s by ring, Nat.mul_mod_right]
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hr2 : r = 2
    · rw [ppaSide_run_ppaSide (by omega) (by omega), ite_eq_left hr2]
      exact decide_eq_false (by omega)
    · rw [ppaSide_bot_ppaSide (by omega), Nat.zero_add]
      exact decide_eq_false (lt_irrefl _)
  · unfold twHeadTop pairTop
    by_cases hr2 : r = 2
    · rw [ite_eq_left hr2, ppaSide_run_ppaSide (by omega) (by omega), ite_eq_left hr2]
      exact decide_eq_true le_rfl
    · rw [ite_eq_right hr2, ppaSide_top_ppaSide h (t := 1) (by omega) (by omega)]
      exact decide_eq_true le_rfl
  · rw [ppaSide_top_ppaSide h (t := 0) (by omega) (by omega)]
    exact decide_eq_false (by omega)
  · rw [ppaSide_top_ppaSide h (t := s) (by omega) (by omega)]
    exact decide_eq_true (by omega)

/-- Every annulus band other than the head band and the top-right climb joins two levels of the
same part. -/
theorem ppaSide_band {r s : ℕ} (h : IsTorusPair r s) (q : ℕ) (hq1 : 1 ≤ q)
    (hq : q < 2 * pairC r s + 2) (hC : q ≠ pairIdxC r s) (hH1 : q ≠ pairIdxH1 r s)
    (hH2 : q ≠ pairIdxH2 r s) :
    ∃ i j : ℕ, (pairBlocks r s).getD q (SBlock.neg 0) = SBlock.band i j ∧ i < j ∧
      j < 2 * pairC r s ∧ ppaSide r s i = ppaSide r s j := by
  obtain ⟨hr, hrs, hc, hE, hb, hE1⟩ := pairAnn_arith h
  have hB := pairRev_idxB h
  have hA : PairArithRv r s (pairC r s) (pairRunDown r s) := ⟨hr, hrs, hc, hE⟩
  have hE2 : r = 2 → pairRunDown r s = 1 := by
    rintro rfl
    simp [pairRunDown]
  simp only [pairIdxC, pairIdxH1, pairIdxH2] at hC hH1 hH2
  have hrun := pairAnnIdx_add_ppaSide h
    (pairAnnIdx_pos_ppaSide h (t := r - 1) (by omega) (by omega))
  rw [show r - 1 + s = s - 1 + r by omega, (pairAnn_chain h (s - 1)).1] at hrun
  rw [pairBlocks_getDRv h q hq, pairBlkRv]
  by_cases h1 : q < r - 2
  · refine ⟨q, 2 * pairC r s - 2 - q, pairBlkAt_reg1Rv h1, by omega, by omega, ?_⟩
    rw [ppaSide_bot_ppaSide h1, ppaSide_top_ppaSide h (t := q + 1) (by omega) (by omega),
      decide_eq_decide]
    have := fun he ↦ pairAnnIdx_inj_ppaSide h (t := 1) (t' := q + 1) (by omega) (by omega) he
    omega
  by_cases h2 : q < r - 2 + pairRunDown r s
  · refine ⟨_, _, pairBlkAt_reg2Rv (by omega) h2, by omega, by omega, ?_⟩
    exact ppaSide_run_eq_ppaSide (by omega) (by omega) (by omega) (by omega)
      fun hr2 ↦ by have := hE2 hr2; omega
  by_cases h3 : q < 2 * pairC r s - s - r
  · refine ⟨_, _, pairBlkAt_reg3Rv (by omega) h3, by omega, by omega, ?_⟩
    exact ppaSide_run_eq_ppaSide (by omega) (by omega) (by omega) (by omega)
      fun hr2 ↦ by omega
  by_cases h4 : q = 2 * pairC r s - s - r
  · refine ⟨_, _, pairBlkAt_reg4Rv hA h4, by omega, by omega, ?_⟩
    rw [ppaSide_run_ppaSide (by omega) (by omega),
      ppaSide_top_ppaSide h (t := r - 1) (by omega) (by omega)]
    by_cases hr2 : r = 2
    · rw [ite_eq_left hr2, decide_eq_decide, show r - 1 = 1 by omega]
      exact ⟨fun _ ↦ le_rfl, fun _ ↦ by omega⟩
    · rw [ite_eq_right hr2, decide_eq_decide]
      have := fun he ↦ pairAnnIdx_inj_ppaSide h (t := 1) (t' := r - 1) (by omega) (by omega) he
      omega
  by_cases h5 : q = 2 * pairC r s - s - r + 1
  · refine ⟨_, _, pairBlkAt_reg5Rv hA h5, by omega, by omega, ?_⟩
    have := (pairAnn_chain h 0).1
    rw [Nat.zero_add] at this
    rw [ppaSide_top_ppaSide h (t := r) (by omega) (by omega),
      ppaSide_top_ppaSide h (t := 0) (by omega) (by omega), this]
  by_cases h6 : q = 2 * pairC r s - s - r + 2
  · omega
  by_cases h7 : q < 2 * pairC r s - r + 1
  · refine ⟨_, _, pairBlkAt_reg7Rv hA (by omega) h7, by omega, by omega, ?_⟩
    obtain ⟨τ, rfl⟩ : ∃ τ, q = pairIdxB r s + 2 + τ := ⟨q - (pairIdxB r s + 2), by omega⟩
    rw [ppaSide_top_ppaSide h (t := τ + r) (by omega) (by omega),
      ppaSide_top_ppaSide h (t := τ) (by omega) (by omega), (pairAnn_chain h τ).1]
  by_cases h8 : q = 2 * pairC r s - r + 1
  · refine ⟨_, _, pairBlkAt_reg8Rv hA h8, by omega, by omega, ?_⟩
    rw [ppaSide_run_ppaSide (by omega) (by omega),
      ppaSide_top_ppaSide h (t := s - 1) (by omega) (by omega)]
    by_cases hr2 : r = 2
    · rw [ite_eq_left hr2, decide_eq_decide]
      rw [show r - 1 = 1 by omega] at hrun
      omega
    · rw [ite_eq_right hr2, decide_eq_decide]
      omega
  by_cases h9 : q = 2 * pairC r s - r + 2
  · omega
  · refine ⟨_, _, pairBlkAt_reg10Rv hA (by omega) (by omega), by omega, by omega, ?_⟩
    have hd := pairAnnIdx_add_ppaSide h
      (pairAnnIdx_pos_ppaSide h (t := 2 * pairC r s - q + 1) (by omega) (by omega))
    rw [ppaSide_bot_ppaSide (by omega),
      ppaSide_top_ppaSide h (t := 2 * pairC r s - q + 1 + s) (by omega) (by omega),
      decide_eq_decide]
    omega

end AJConjecture
