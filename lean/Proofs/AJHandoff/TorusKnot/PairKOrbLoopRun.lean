import Mathlib
import AJHandoff.TorusKnot.PairKOrbStage

/-!
# Strand loops of `pairBlocks r s`: the runs and the window feet

For the positions `r - 1 ≤ t ≤ b₀ + r - 2` (`b₀ = 2c - s - r`) the strand loop is `pairOrbCore`:

* the decreasing run `r - 1 ≤ t ≤ c - s`: `D' R_(s-1) X_t A`, where `X_t` is the run block of
  level `t` (`pairIdxRun r s t`), `D' = D'_(r-3) ⋯ D'_0`, `A = A_(r-3) ⋯ A_0`; this is the gap
  factor of level `t`, hence trivial for a fixed tuple;
* the increasing run and `b₀` (`c - s + 1 ≤ t ≤ b₀`): `D' R_(s-1) A`;
* the window feet `t = b₀ + p`, `1 ≤ p ≤ r - 2`: `D'_(r-3) ⋯ D'_(p-1) · A_(r-3-p) ⋯ A_0`.

Route: `stLoop_pairBlocks_stages`; evaluate the eleven factors with the pattern lemmas
(`stLoop_orbSpread` for stage 1, `stLoop_orbStair` with `d = r` for stage 4, `stLoop_orbRunUp`,
`stLoop_orbRunDown`, `stLoop_orbNested`, `stLoop_singleton_orb` for the one-block stages), the
positions `pairOrbPos` with the strand-map pattern lemmas (stage by stage, as `pair_head` /
`pair_tail` in `AJHandoff.TorusKnot.PairKConnected`), and `loopAt_pairOrbStage`; the filtered
range products become `descProd` (`descProd_eq_prod_range`-style reindexing). Checked by computer
(`pairOrbCheckLoop` in `AJHandoff.TorusKnot.PairKOrbDefs`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

set_option linter.unusedSimpArgs false in
/-- Split the conditionals of the goal and close every branch by `omega`. -/
local macro "orb_ifs" : tactic => `(tactic| (split_ifs <;> omega))

set_option linter.unusedSimpArgs false in
/-- The strand loop of a position of the decreasing run. -/
private theorem stLoop_pairBlocks_runDown {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {t : ℕ} (h1 : r ≤ t + 1)
    (ha : t + s ≤ pairC r s) :
    stLoop (pairStrands r s) (pairBlocks r s) f t =
      descProd (fun j ↦ loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxDp r s j)) 0 (r - 2) *
        loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (s - 1)) *
        loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxRun r s t) *
        descProd (loopAt (pairStrands r s) (pairBlocks r s) f) 0 (r - 2) := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairOrbStage_arith h
  have hc : s ≤ pairC r s := (pairOrb_arith h).2.2.1
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hz : pairRunUp r s = pairC r s - r - 1 := rfl
  have e1 : pairOrbPos r s 1 t = t := by
    rw [pairOrbPos_succ, pairOrbPos_zero, stPerm_pairOrbStage_zero h]
    orb_ifs
  have e2 : pairOrbPos r s 2 t = t := by
    rw [pairOrbPos_succ, e1, stPerm_pairOrbStage_one h]
    orb_ifs
  have e3 : pairOrbPos r s 3 t = t := by
    rw [pairOrbPos_succ, e2, stPerm_pairOrbStage_two h]
    clear e1
    orb_ifs
  have e4 : pairOrbPos r s 4 t = t := by
    rw [pairOrbPos_succ, e3, stPerm_pairOrbStage_three h]
    clear e1 e2
    orb_ifs
  have e5 : pairOrbPos r s 5 t = t := by
    rw [pairOrbPos_succ, e4, stPerm_pairOrbStage_four h]
    clear e1 e2 e3
    orb_ifs
  have e6 : pairOrbPos r s 6 t = t := by
    rw [pairOrbPos_succ, e5, stPerm_pairOrbStage_five h]
    clear e1 e2 e3 e4
    orb_ifs
  have e7 : pairOrbPos r s 7 t = t := by
    rw [pairOrbPos_succ, e6, stPerm_pairOrbStage_six h]
    clear e1 e2 e3 e4 e5
    orb_ifs
  have e8 : pairOrbPos r s 8 t = t := by
    rw [pairOrbPos_succ, e7, stPerm_pairOrbStage_seven h]
    clear e1 e2 e3 e4 e5 e6
    orb_ifs
  have e9 : pairOrbPos r s 9 t = t := by
    rw [pairOrbPos_succ, e8, stPerm_pairOrbStage_eight h]
    clear e1 e2 e3 e4 e5 e6 e7
    orb_ifs
  have e10 : pairOrbPos r s 10 t = t - 1 := by
    rw [pairOrbPos_succ, e9, stPerm_pairOrbStage_nine h]
    clear e1 e2 e3 e4 e5 e6 e7 e8
    orb_ifs
  rw [stLoop_pairBlocks_eleven, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  rw [stLoop_pairOrbStage_zero_off h f (p := t) (by omega),
    stLoop_pairOrbStage_one_eq h f (p := t) (lo := 0)
      (len := r - 2) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_two_off h f (p := t) (by omega),
    stLoop_pairOrbStage_three_on h f (p := t) (by omega),
    stLoop_pairOrbStage_four_eq h f (p := t) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by orb_ifs),
    stLoop_pairOrbStage_five_off h f (p := t) (by omega),
    stLoop_pairOrbStage_six_off h f (p := t) (by omega),
    stLoop_pairOrbStage_seven_off h f (p := t) (by omega),
    stLoop_pairOrbStage_eight_eq h f (p := t) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_nine_eq h f (p := t) (lo := pairC r s - s + 1 - t)
      (len := 1) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_ten_eq h f (p := t - 1) (lo := 0)
      (len := r - 2) (by omega) (fun j hj ↦ by omega)]
  simp only [one_mul, mul_one, descProd_zero_orb, descProd_one_orb]
  rw [show pairIdxRun r s t = r - 2 + (pairC r s - s + 1 - t) by
    unfold pairIdxRun; rw [ite_eq_left (by omega)]; omega]

set_option linter.unusedSimpArgs false in
/-- The strand loop of a position of the increasing run below `b₀`. -/
private theorem stLoop_pairBlocks_runUp {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {t : ℕ} (ha : pairC r s < t + s)
    (hb : t + s + r < 2 * pairC r s) :
    stLoop (pairStrands r s) (pairBlocks r s) f t =
      descProd (fun j ↦ loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxDp r s j)) 0 (r - 2) *
        loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (s - 1)) *
        descProd (loopAt (pairStrands r s) (pairBlocks r s) f) 0 (r - 2) := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairOrbStage_arith h
  have hc : s ≤ pairC r s := (pairOrb_arith h).2.2.1
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hz : pairRunUp r s = pairC r s - r - 1 := rfl
  have e1 : pairOrbPos r s 1 t = t := by
    rw [pairOrbPos_succ, pairOrbPos_zero, stPerm_pairOrbStage_zero h]
    orb_ifs
  have e2 : pairOrbPos r s 2 t = t := by
    rw [pairOrbPos_succ, e1, stPerm_pairOrbStage_one h]
    orb_ifs
  have e3 : pairOrbPos r s 3 t = t := by
    rw [pairOrbPos_succ, e2, stPerm_pairOrbStage_two h]
    clear e1
    orb_ifs
  have e4 : pairOrbPos r s 4 t = t := by
    rw [pairOrbPos_succ, e3, stPerm_pairOrbStage_three h]
    clear e1 e2
    orb_ifs
  have e5 : pairOrbPos r s 5 t = t := by
    rw [pairOrbPos_succ, e4, stPerm_pairOrbStage_four h]
    clear e1 e2 e3
    orb_ifs
  have e6 : pairOrbPos r s 6 t = t := by
    rw [pairOrbPos_succ, e5, stPerm_pairOrbStage_five h]
    clear e1 e2 e3 e4
    orb_ifs
  have e7 : pairOrbPos r s 7 t = t := by
    rw [pairOrbPos_succ, e6, stPerm_pairOrbStage_six h]
    clear e1 e2 e3 e4 e5
    orb_ifs
  have e8 : pairOrbPos r s 8 t = t := by
    rw [pairOrbPos_succ, e7, stPerm_pairOrbStage_seven h]
    clear e1 e2 e3 e4 e5 e6
    orb_ifs
  have e9 : pairOrbPos r s 9 t = t + 1 := by
    rw [pairOrbPos_succ, e8, stPerm_pairOrbStage_eight h]
    clear e1 e2 e3 e4 e5 e6 e7
    orb_ifs
  have e10 : pairOrbPos r s 10 t = t + 1 := by
    rw [pairOrbPos_succ, e9, stPerm_pairOrbStage_nine h]
    clear e1 e2 e3 e4 e5 e6 e7 e8
    orb_ifs
  rw [stLoop_pairBlocks_eleven, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  rw [stLoop_pairOrbStage_zero_off h f (p := t) (by omega),
    stLoop_pairOrbStage_one_eq h f (p := t) (lo := 0)
      (len := r - 2) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_two_off h f (p := t) (by omega),
    stLoop_pairOrbStage_three_on h f (p := t) (by omega),
    stLoop_pairOrbStage_four_eq h f (p := t) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by orb_ifs),
    stLoop_pairOrbStage_five_off h f (p := t) (by omega),
    stLoop_pairOrbStage_six_off h f (p := t) (by omega),
    stLoop_pairOrbStage_seven_off h f (p := t) (by omega),
    stLoop_pairOrbStage_eight_eq h f (p := t) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_nine_eq h f (p := t + 1) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_ten_eq h f (p := t + 1) (lo := 0)
      (len := r - 2) (by omega) (fun j hj ↦ by omega)]
  simp only [one_mul, mul_one, descProd_zero_orb, descProd_one_orb]

set_option linter.unusedSimpArgs false in
/-- The strand loop of the position `b₀`. -/
private theorem stLoop_pairBlocks_runB0 {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {t : ℕ} (hb : t + s + r = 2 * pairC r s) :
    stLoop (pairStrands r s) (pairBlocks r s) f t =
      descProd (fun j ↦ loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxDp r s j)) 0 (r - 2) *
        loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxR r s (s - 1)) *
        descProd (loopAt (pairStrands r s) (pairBlocks r s) f) 0 (r - 2) := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairOrbStage_arith h
  have hc : s ≤ pairC r s := (pairOrb_arith h).2.2.1
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hz : pairRunUp r s = pairC r s - r - 1 := rfl
  have e1 : pairOrbPos r s 1 t = t := by
    rw [pairOrbPos_succ, pairOrbPos_zero, stPerm_pairOrbStage_zero h]
    orb_ifs
  have e2 : pairOrbPos r s 2 t = t := by
    rw [pairOrbPos_succ, e1, stPerm_pairOrbStage_one h]
    orb_ifs
  have e3 : pairOrbPos r s 3 t = t := by
    rw [pairOrbPos_succ, e2, stPerm_pairOrbStage_two h]
    clear e1
    orb_ifs
  have e4 : pairOrbPos r s 4 t = t := by
    rw [pairOrbPos_succ, e3, stPerm_pairOrbStage_three h]
    clear e1 e2
    orb_ifs
  have e5 : pairOrbPos r s 5 t = t := by
    rw [pairOrbPos_succ, e4, stPerm_pairOrbStage_four h]
    clear e1 e2 e3
    orb_ifs
  have e6 : pairOrbPos r s 6 t = t := by
    rw [pairOrbPos_succ, e5, stPerm_pairOrbStage_five h]
    clear e1 e2 e3 e4
    orb_ifs
  have e7 : pairOrbPos r s 7 t = t := by
    rw [pairOrbPos_succ, e6, stPerm_pairOrbStage_six h]
    clear e1 e2 e3 e4 e5
    orb_ifs
  have e8 : pairOrbPos r s 8 t = 2 * pairC r s - r := by
    rw [pairOrbPos_succ, e7, stPerm_pairOrbStage_seven h]
    clear e1 e2 e3 e4 e5 e6
    orb_ifs
  have e9 : pairOrbPos r s 9 t = 2 * pairC r s - r := by
    rw [pairOrbPos_succ, e8, stPerm_pairOrbStage_eight h]
    clear e1 e2 e3 e4 e5 e6 e7
    orb_ifs
  have e10 : pairOrbPos r s 10 t = 2 * pairC r s - r := by
    rw [pairOrbPos_succ, e9, stPerm_pairOrbStage_nine h]
    clear e1 e2 e3 e4 e5 e6 e7 e8
    orb_ifs
  rw [stLoop_pairBlocks_eleven, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  rw [stLoop_pairOrbStage_zero_off h f (p := t) (by omega),
    stLoop_pairOrbStage_one_eq h f (p := t) (lo := 0)
      (len := r - 2) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_two_off h f (p := t) (by omega),
    stLoop_pairOrbStage_three_on h f (p := t) (by omega),
    stLoop_pairOrbStage_four_eq h f (p := t) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by orb_ifs),
    stLoop_pairOrbStage_five_off h f (p := t) (by omega),
    stLoop_pairOrbStage_six_off h f (p := t) (by omega),
    stLoop_pairOrbStage_seven_off h f (p := t) (by omega),
    stLoop_pairOrbStage_eight_eq h f (p := 2 * pairC r s - r) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_nine_eq h f (p := 2 * pairC r s - r) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_ten_eq h f (p := 2 * pairC r s - r) (lo := 0)
      (len := r - 2) (by omega) (fun j hj ↦ by omega)]
  simp only [one_mul, mul_one, descProd_zero_orb, descProd_one_orb]

set_option linter.unusedSimpArgs false in
/-- The strand loop of a window foot `b₀ + p`, `1 ≤ p ≤ r - 2`. -/
private theorem stLoop_pairBlocks_runFoot {r s : ℕ} (h : IsTorusPair r s)
    (f : Fin (pairStrands r s) → G) {t : ℕ} (hb : 2 * pairC r s < t + s + r)
    (h2 : t + s + 2 ≤ 2 * pairC r s) :
    stLoop (pairStrands r s) (pairBlocks r s) f t =
      descProd (fun j ↦ loopAt (pairStrands r s) (pairBlocks r s) f (pairIdxDp r s j))
        (pairOrbFoot r s t - 1) (r - 1 - pairOrbFoot r s t) *
        descProd (loopAt (pairStrands r s) (pairBlocks r s) f) 0 (r - 2 - pairOrbFoot r s t) := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairOrbStage_arith h
  have hc : s ≤ pairC r s := (pairOrb_arith h).2.2.1
  have hT : pairTop r s = 2 * pairC r s - 1 := rfl
  have hz : pairRunUp r s = pairC r s - r - 1 := rfl
  have hF : pairOrbFoot r s t = t + s + r - 2 * pairC r s := rfl
  have e1 : pairOrbPos r s 1 t = t := by
    rw [pairOrbPos_succ, pairOrbPos_zero, stPerm_pairOrbStage_zero h]
    orb_ifs
  have e2 : pairOrbPos r s 2 t = 2 * pairC r s - s - 2 - t := by
    rw [pairOrbPos_succ, e1, stPerm_pairOrbStage_one h]
    orb_ifs
  have e3 : pairOrbPos r s 3 t = 2 * pairC r s - s - 2 - t := by
    rw [pairOrbPos_succ, e2, stPerm_pairOrbStage_two h]
    clear e1
    orb_ifs
  have e4 : pairOrbPos r s 4 t = 2 * pairC r s - s - 2 - t := by
    rw [pairOrbPos_succ, e3, stPerm_pairOrbStage_three h]
    clear e1 e2
    orb_ifs
  have e5 : pairOrbPos r s 5 t = 2 * pairC r s - s - 2 - t := by
    rw [pairOrbPos_succ, e4, stPerm_pairOrbStage_four h]
    clear e1 e2 e3
    orb_ifs
  have e6 : pairOrbPos r s 6 t = 2 * pairC r s - s - 2 - t := by
    rw [pairOrbPos_succ, e5, stPerm_pairOrbStage_five h]
    clear e1 e2 e3 e4
    orb_ifs
  have e7 : pairOrbPos r s 7 t = 2 * pairC r s - s - 2 - t := by
    rw [pairOrbPos_succ, e6, stPerm_pairOrbStage_six h]
    clear e1 e2 e3 e4 e5
    orb_ifs
  have e8 : pairOrbPos r s 8 t = 2 * pairC r s - s - 2 - t := by
    rw [pairOrbPos_succ, e7, stPerm_pairOrbStage_seven h]
    clear e1 e2 e3 e4 e5 e6
    orb_ifs
  have e9 : pairOrbPos r s 9 t = 2 * pairC r s - s - 2 - t := by
    rw [pairOrbPos_succ, e8, stPerm_pairOrbStage_eight h]
    clear e1 e2 e3 e4 e5 e6 e7
    orb_ifs
  have e10 : pairOrbPos r s 10 t = 2 * pairC r s - s - 2 - t := by
    rw [pairOrbPos_succ, e9, stPerm_pairOrbStage_nine h]
    clear e1 e2 e3 e4 e5 e6 e7 e8
    orb_ifs
  rw [stLoop_pairBlocks_eleven, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  rw [stLoop_pairOrbStage_zero_off h f (p := t) (by omega),
    stLoop_pairOrbStage_one_eq h f (p := t) (lo := pairOrbFoot r s t - 1)
      (len := r - 1 - pairOrbFoot r s t) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_two_off h f (p := 2 * pairC r s - s - 2 - t) (by omega),
    stLoop_pairOrbStage_three_off h f (p := 2 * pairC r s - s - 2 - t) (by omega),
    stLoop_pairOrbStage_four_eq h f (p := 2 * pairC r s - s - 2 - t) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by orb_ifs),
    stLoop_pairOrbStage_five_off h f (p := 2 * pairC r s - s - 2 - t) (by omega),
    stLoop_pairOrbStage_six_off h f (p := 2 * pairC r s - s - 2 - t) (by omega),
    stLoop_pairOrbStage_seven_off h f (p := 2 * pairC r s - s - 2 - t) (by omega),
    stLoop_pairOrbStage_eight_eq h f (p := 2 * pairC r s - s - 2 - t) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_nine_eq h f (p := 2 * pairC r s - s - 2 - t) (lo := 0)
      (len := 0) (by omega) (fun j hj ↦ by omega),
    stLoop_pairOrbStage_ten_eq h f (p := 2 * pairC r s - s - 2 - t) (lo := 0)
      (len := r - 2 - pairOrbFoot r s t) (by omega) (fun j hj ↦ by omega)]
  simp only [one_mul, mul_one, descProd_zero_orb, descProd_one_orb]

/-- The strand loops of the decreasing run, the increasing run, `b₀` and the window feet. -/
theorem stLoop_pairBlocks_run {r s : ℕ} (h : IsTorusPair r s) (f : Fin (pairStrands r s) → G)
    {t : ℕ} (h1 : r ≤ t + 1) (h2 : t + s + 2 ≤ 2 * pairC r s) :
    stLoop (pairStrands r s) (pairBlocks r s) f t =
      pairOrbCore r s (loopAt (pairStrands r s) (pairBlocks r s) f) t := by
  obtain ⟨hr, hrs, hE1, hE⟩ := pairOrbStage_arith h
  have hc : s ≤ pairC r s := (pairOrb_arith h).2.2.1
  unfold pairOrbCore
  rw [ite_eq_right (show ¬ (t + 2 ≤ r ∨ t = 2 * pairC r s) by omega)]
  by_cases ha : t + s ≤ pairC r s
  · rw [ite_eq_left ha, stLoop_pairBlocks_runDown h f h1 ha]
  rw [ite_eq_right ha]
  by_cases hb : t + s + r ≤ 2 * pairC r s
  · rw [ite_eq_left hb]
    by_cases hb' : t + s + r < 2 * pairC r s
    · rw [stLoop_pairBlocks_runUp h f (by omega) hb']
    · rw [stLoop_pairBlocks_runB0 h f (by omega)]
  rw [ite_eq_right hb, ite_eq_left h2, stLoop_pairBlocks_runFoot h f (by omega) h2]

end AJConjecture
